import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block1Chunk0Sources : List Nat :=
  [   5248, 5249, 5250, 5251, 5252, 5253, 5254, 5255,
   5256, 5257, 5258, 5259, 5260, 5261, 5262, 5263]

def tttLargeFiber50Row64 : TripleComponentParentRow :=
  tripleRow 5248 5184 157 156 148 156 148 148
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row65 : TripleComponentParentRow :=
  tripleRow 5249 5185 157 156 149 156 148 149
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row66 : TripleComponentParentRow :=
  tripleRow 5250 5186 157 156 150 156 148 150
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row67 : TripleComponentParentRow :=
  tripleRow 5251 5187 157 156 151 156 148 151
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row68 : TripleComponentParentRow :=
  tripleRow 5252 5188 157 156 164 156 148 164
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row69 : TripleComponentParentRow :=
  tripleRow 5253 5189 157 156 165 156 148 165
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row70 : TripleComponentParentRow :=
  tripleRow 5254 5190 157 156 166 156 148 166
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row71 : TripleComponentParentRow :=
  tripleRow 5255 5191 157 156 167 156 148 167
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row72 : TripleComponentParentRow :=
  tripleRow 5256 5192 157 157 156 156 149 156
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row73 : TripleComponentParentRow :=
  tripleRow 5257 5193 157 157 157 156 149 157
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row74 : TripleComponentParentRow :=
  tripleRow 5258 5194 157 157 158 156 149 158
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row75 : TripleComponentParentRow :=
  tripleRow 5259 5195 157 157 159 156 149 159
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row76 : TripleComponentParentRow :=
  tripleRow 5260 5196 157 157 172 156 149 172
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row77 : TripleComponentParentRow :=
  tripleRow 5261 5197 157 157 173 156 149 173
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row78 : TripleComponentParentRow :=
  tripleRow 5262 5198 157 157 174 156 149 174
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row79 : TripleComponentParentRow :=
  tripleRow 5263 5199 157 157 175 156 149 175
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row64
  , tttLargeFiber50Row65
  , tttLargeFiber50Row66
  , tttLargeFiber50Row67
  , tttLargeFiber50Row68
  , tttLargeFiber50Row69
  , tttLargeFiber50Row70
  , tttLargeFiber50Row71
  , tttLargeFiber50Row72
  , tttLargeFiber50Row73
  , tttLargeFiber50Row74
  , tttLargeFiber50Row75
  , tttLargeFiber50Row76
  , tttLargeFiber50Row77
  , tttLargeFiber50Row78
  , tttLargeFiber50Row79
  ]

def tttLargeFiber50Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber50Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber50Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber50Block1Chunk0Sources

theorem tttLargeFiber50Block1Chunk0SourcesCheck_ok :
    tttLargeFiber50Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber50Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block1Chunk0RowValid
    (listGetD tttLargeFiber50Block1Chunk0Rows i default)

def tttLargeFiber50Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block1Chunk0Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block1Chunk0Sources 0 0 == 5248
      && tttLargeFiber50ParentOf 5248 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (1 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block1Chunk0Sources 1 0 == 5249
      && tttLargeFiber50ParentOf 5249 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block1Chunk0Sources 2 0 == 5250
      && tttLargeFiber50ParentOf 5250 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block1Chunk0Sources 3 0 == 5251
      && tttLargeFiber50ParentOf 5251 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block1Chunk0Sources 4 0 == 5252
      && tttLargeFiber50ParentOf 5252 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block1Chunk0Sources 5 0 == 5253
      && tttLargeFiber50ParentOf 5253 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block1Chunk0Sources 6 0 == 5254
      && tttLargeFiber50ParentOf 5254 == 5190
      && tttLargeFiber50ParentOf 5190 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block1Chunk0Sources 7 0 == 5255
      && tttLargeFiber50ParentOf 5255 == 5191
      && tttLargeFiber50ParentOf 5191 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block1Chunk0Sources 8 0 == 5256
      && tttLargeFiber50ParentOf 5256 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block1Chunk0Sources 9 0 == 5257
      && tttLargeFiber50ParentOf 5257 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block1Chunk0Sources 10 0 == 5258
      && tttLargeFiber50ParentOf 5258 == 5194
      && tttLargeFiber50ParentOf 5194 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block1Chunk0Sources 11 0 == 5259
      && tttLargeFiber50ParentOf 5259 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block1Chunk0Sources 12 0 == 5260
      && tttLargeFiber50ParentOf 5260 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block1Chunk0Sources 13 0 == 5261
      && tttLargeFiber50ParentOf 5261 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block1Chunk0Sources 14 0 == 5262
      && tttLargeFiber50ParentOf 5262 == 5198
      && tttLargeFiber50ParentOf 5198 == 5190
      && tttLargeFiber50ParentOf 5190 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block1Chunk0Sources 15 0 == 5263
      && tttLargeFiber50ParentOf 5263 == 5199
      && tttLargeFiber50ParentOf 5199 == 5191
      && tttLargeFiber50ParentOf 5191 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block1Chunk0Row_0_ok :
    tttLargeFiber50Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_1_ok :
    tttLargeFiber50Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_2_ok :
    tttLargeFiber50Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_3_ok :
    tttLargeFiber50Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_4_ok :
    tttLargeFiber50Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_5_ok :
    tttLargeFiber50Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_6_ok :
    tttLargeFiber50Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_7_ok :
    tttLargeFiber50Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_8_ok :
    tttLargeFiber50Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_9_ok :
    tttLargeFiber50Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_10_ok :
    tttLargeFiber50Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_11_ok :
    tttLargeFiber50Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_12_ok :
    tttLargeFiber50Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_13_ok :
    tttLargeFiber50Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_14_ok :
    tttLargeFiber50Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0Row_15_ok :
    tttLargeFiber50Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_0_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_1_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_2_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_3_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_4_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_5_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_6_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_7_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_8_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_9_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_10_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_11_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_12_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_13_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_14_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentMap_15_ok :
    tttLargeFiber50Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_0_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_1_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_2_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_3_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_4_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_5_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_6_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_7_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_8_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_9_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_10_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_11_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_12_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_13_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_14_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk0ParentPath_15_ok :
    tttLargeFiber50Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber50Block1Chunk0RowCheck 0
    && tttLargeFiber50Block1Chunk0RowCheck 1
    && tttLargeFiber50Block1Chunk0RowCheck 2
    && tttLargeFiber50Block1Chunk0RowCheck 3
    && tttLargeFiber50Block1Chunk0RowCheck 4
    && tttLargeFiber50Block1Chunk0RowCheck 5
    && tttLargeFiber50Block1Chunk0RowCheck 6
    && tttLargeFiber50Block1Chunk0RowCheck 7
    && tttLargeFiber50Block1Chunk0RowCheck 8
    && tttLargeFiber50Block1Chunk0RowCheck 9
    && tttLargeFiber50Block1Chunk0RowCheck 10
    && tttLargeFiber50Block1Chunk0RowCheck 11
    && tttLargeFiber50Block1Chunk0RowCheck 12
    && tttLargeFiber50Block1Chunk0RowCheck 13
    && tttLargeFiber50Block1Chunk0RowCheck 14
    && tttLargeFiber50Block1Chunk0RowCheck 15

theorem tttLargeFiber50Block1Chunk0RowsAudit_ok :
    tttLargeFiber50Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber50Block1Chunk0RowsAudit,
    tttLargeFiber50Block1Chunk0Row_0_ok,
    tttLargeFiber50Block1Chunk0Row_1_ok,
    tttLargeFiber50Block1Chunk0Row_2_ok,
    tttLargeFiber50Block1Chunk0Row_3_ok,
    tttLargeFiber50Block1Chunk0Row_4_ok,
    tttLargeFiber50Block1Chunk0Row_5_ok,
    tttLargeFiber50Block1Chunk0Row_6_ok,
    tttLargeFiber50Block1Chunk0Row_7_ok,
    tttLargeFiber50Block1Chunk0Row_8_ok,
    tttLargeFiber50Block1Chunk0Row_9_ok,
    tttLargeFiber50Block1Chunk0Row_10_ok,
    tttLargeFiber50Block1Chunk0Row_11_ok,
    tttLargeFiber50Block1Chunk0Row_12_ok,
    tttLargeFiber50Block1Chunk0Row_13_ok,
    tttLargeFiber50Block1Chunk0Row_14_ok,
    tttLargeFiber50Block1Chunk0Row_15_ok]

def tttLargeFiber50Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber50Block1Chunk0ParentMapCheck 0
    && tttLargeFiber50Block1Chunk0ParentMapCheck 1
    && tttLargeFiber50Block1Chunk0ParentMapCheck 2
    && tttLargeFiber50Block1Chunk0ParentMapCheck 3
    && tttLargeFiber50Block1Chunk0ParentMapCheck 4
    && tttLargeFiber50Block1Chunk0ParentMapCheck 5
    && tttLargeFiber50Block1Chunk0ParentMapCheck 6
    && tttLargeFiber50Block1Chunk0ParentMapCheck 7
    && tttLargeFiber50Block1Chunk0ParentMapCheck 8
    && tttLargeFiber50Block1Chunk0ParentMapCheck 9
    && tttLargeFiber50Block1Chunk0ParentMapCheck 10
    && tttLargeFiber50Block1Chunk0ParentMapCheck 11
    && tttLargeFiber50Block1Chunk0ParentMapCheck 12
    && tttLargeFiber50Block1Chunk0ParentMapCheck 13
    && tttLargeFiber50Block1Chunk0ParentMapCheck 14
    && tttLargeFiber50Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber50Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber50Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber50Block1Chunk0ParentMapAudit,
    tttLargeFiber50Block1Chunk0ParentMap_0_ok,
    tttLargeFiber50Block1Chunk0ParentMap_1_ok,
    tttLargeFiber50Block1Chunk0ParentMap_2_ok,
    tttLargeFiber50Block1Chunk0ParentMap_3_ok,
    tttLargeFiber50Block1Chunk0ParentMap_4_ok,
    tttLargeFiber50Block1Chunk0ParentMap_5_ok,
    tttLargeFiber50Block1Chunk0ParentMap_6_ok,
    tttLargeFiber50Block1Chunk0ParentMap_7_ok,
    tttLargeFiber50Block1Chunk0ParentMap_8_ok,
    tttLargeFiber50Block1Chunk0ParentMap_9_ok,
    tttLargeFiber50Block1Chunk0ParentMap_10_ok,
    tttLargeFiber50Block1Chunk0ParentMap_11_ok,
    tttLargeFiber50Block1Chunk0ParentMap_12_ok,
    tttLargeFiber50Block1Chunk0ParentMap_13_ok,
    tttLargeFiber50Block1Chunk0ParentMap_14_ok,
    tttLargeFiber50Block1Chunk0ParentMap_15_ok]

def tttLargeFiber50Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber50Block1Chunk0ParentPathCheck 0
    && tttLargeFiber50Block1Chunk0ParentPathCheck 1
    && tttLargeFiber50Block1Chunk0ParentPathCheck 2
    && tttLargeFiber50Block1Chunk0ParentPathCheck 3
    && tttLargeFiber50Block1Chunk0ParentPathCheck 4
    && tttLargeFiber50Block1Chunk0ParentPathCheck 5
    && tttLargeFiber50Block1Chunk0ParentPathCheck 6
    && tttLargeFiber50Block1Chunk0ParentPathCheck 7
    && tttLargeFiber50Block1Chunk0ParentPathCheck 8
    && tttLargeFiber50Block1Chunk0ParentPathCheck 9
    && tttLargeFiber50Block1Chunk0ParentPathCheck 10
    && tttLargeFiber50Block1Chunk0ParentPathCheck 11
    && tttLargeFiber50Block1Chunk0ParentPathCheck 12
    && tttLargeFiber50Block1Chunk0ParentPathCheck 13
    && tttLargeFiber50Block1Chunk0ParentPathCheck 14
    && tttLargeFiber50Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber50Block1Chunk0ParentsAudit_ok :
    tttLargeFiber50Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber50Block1Chunk0ParentsAudit,
    tttLargeFiber50Block1Chunk0ParentPath_0_ok,
    tttLargeFiber50Block1Chunk0ParentPath_1_ok,
    tttLargeFiber50Block1Chunk0ParentPath_2_ok,
    tttLargeFiber50Block1Chunk0ParentPath_3_ok,
    tttLargeFiber50Block1Chunk0ParentPath_4_ok,
    tttLargeFiber50Block1Chunk0ParentPath_5_ok,
    tttLargeFiber50Block1Chunk0ParentPath_6_ok,
    tttLargeFiber50Block1Chunk0ParentPath_7_ok,
    tttLargeFiber50Block1Chunk0ParentPath_8_ok,
    tttLargeFiber50Block1Chunk0ParentPath_9_ok,
    tttLargeFiber50Block1Chunk0ParentPath_10_ok,
    tttLargeFiber50Block1Chunk0ParentPath_11_ok,
    tttLargeFiber50Block1Chunk0ParentPath_12_ok,
    tttLargeFiber50Block1Chunk0ParentPath_13_ok,
    tttLargeFiber50Block1Chunk0ParentPath_14_ok,
    tttLargeFiber50Block1Chunk0ParentPath_15_ok]

def tttLargeFiber50Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block1Chunk0SourcesCheck &&
    tttLargeFiber50Block1Chunk0RowsAudit &&
    tttLargeFiber50Block1Chunk0ParentMapAudit &&
    tttLargeFiber50Block1Chunk0ParentsAudit

theorem tttLargeFiber50Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber50Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block1Chunk0SourcesCheck_ok,
    tttLargeFiber50Block1Chunk0RowsAudit_ok,
    tttLargeFiber50Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber50Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
