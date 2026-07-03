import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block0Chunk0Sources : List Nat :=
  [   5184, 5185, 5186, 5187, 5188, 5189, 5190, 5191,
   5192, 5193, 5194, 5195, 5196, 5197, 5198, 5199]

def tttLargeFiber50Row0 : TripleComponentParentRow :=
  tripleRow 5184 5184 156 148 148 156 148 148
    default
    []

def tttLargeFiber50Row1 : TripleComponentParentRow :=
  tripleRow 5185 5184 156 148 149 156 148 148
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Row2 : TripleComponentParentRow :=
  tripleRow 5186 5185 156 148 150 156 148 149
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row3 : TripleComponentParentRow :=
  tripleRow 5187 5184 156 148 151 156 148 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row4 : TripleComponentParentRow :=
  tripleRow 5188 5184 156 148 164 156 148 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row5 : TripleComponentParentRow :=
  tripleRow 5189 5185 156 148 165 156 148 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Row6 : TripleComponentParentRow :=
  tripleRow 5190 5188 156 148 166 156 148 164
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row7 : TripleComponentParentRow :=
  tripleRow 5191 5187 156 148 167 156 148 151
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row8 : TripleComponentParentRow :=
  tripleRow 5192 5184 156 149 156 156 148 148
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Row9 : TripleComponentParentRow :=
  tripleRow 5193 5185 156 149 157 156 148 149
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Row10 : TripleComponentParentRow :=
  tripleRow 5194 5186 156 149 158 156 148 150
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Row11 : TripleComponentParentRow :=
  tripleRow 5195 5187 156 149 159 156 148 151
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Row12 : TripleComponentParentRow :=
  tripleRow 5196 5188 156 149 172 156 148 164
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Row13 : TripleComponentParentRow :=
  tripleRow 5197 5189 156 149 173 156 148 165
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Row14 : TripleComponentParentRow :=
  tripleRow 5198 5190 156 149 174 156 148 166
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Row15 : TripleComponentParentRow :=
  tripleRow 5199 5191 156 149 175 156 148 167
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber50Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row0
  , tttLargeFiber50Row1
  , tttLargeFiber50Row2
  , tttLargeFiber50Row3
  , tttLargeFiber50Row4
  , tttLargeFiber50Row5
  , tttLargeFiber50Row6
  , tttLargeFiber50Row7
  , tttLargeFiber50Row8
  , tttLargeFiber50Row9
  , tttLargeFiber50Row10
  , tttLargeFiber50Row11
  , tttLargeFiber50Row12
  , tttLargeFiber50Row13
  , tttLargeFiber50Row14
  , tttLargeFiber50Row15
  ]

def tttLargeFiber50Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber50Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber50Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber50Block0Chunk0Sources

theorem tttLargeFiber50Block0Chunk0SourcesCheck_ok :
    tttLargeFiber50Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber50Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block0Chunk0RowValid
    (listGetD tttLargeFiber50Block0Chunk0Rows i default)

def tttLargeFiber50Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block0Chunk0Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block0Chunk0Sources 0 0 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (0 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block0Chunk0Sources 1 0 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (1 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block0Chunk0Sources 2 0 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block0Chunk0Sources 3 0 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (1 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block0Chunk0Sources 4 0 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (1 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block0Chunk0Sources 5 0 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block0Chunk0Sources 6 0 == 5190
      && tttLargeFiber50ParentOf 5190 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block0Chunk0Sources 7 0 == 5191
      && tttLargeFiber50ParentOf 5191 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block0Chunk0Sources 8 0 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (1 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block0Chunk0Sources 9 0 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block0Chunk0Sources 10 0 == 5194
      && tttLargeFiber50ParentOf 5194 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block0Chunk0Sources 11 0 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block0Chunk0Sources 12 0 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block0Chunk0Sources 13 0 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block0Chunk0Sources 14 0 == 5198
      && tttLargeFiber50ParentOf 5198 == 5190
      && tttLargeFiber50ParentOf 5190 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block0Chunk0Sources 15 0 == 5199
      && tttLargeFiber50ParentOf 5199 == 5191
      && tttLargeFiber50ParentOf 5191 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block0Chunk0Row_0_ok :
    tttLargeFiber50Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_1_ok :
    tttLargeFiber50Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_2_ok :
    tttLargeFiber50Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_3_ok :
    tttLargeFiber50Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_4_ok :
    tttLargeFiber50Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_5_ok :
    tttLargeFiber50Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_6_ok :
    tttLargeFiber50Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_7_ok :
    tttLargeFiber50Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_8_ok :
    tttLargeFiber50Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_9_ok :
    tttLargeFiber50Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_10_ok :
    tttLargeFiber50Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_11_ok :
    tttLargeFiber50Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_12_ok :
    tttLargeFiber50Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_13_ok :
    tttLargeFiber50Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_14_ok :
    tttLargeFiber50Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0Row_15_ok :
    tttLargeFiber50Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_0_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_1_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_2_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_3_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_4_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_5_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_6_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_7_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_8_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_9_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_10_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_11_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_12_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_13_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_14_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentMap_15_ok :
    tttLargeFiber50Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_0_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_1_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_2_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_3_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_4_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_5_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_6_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_7_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_8_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_9_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_10_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_11_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_12_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_13_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_14_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block0Chunk0ParentPath_15_ok :
    tttLargeFiber50Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber50Block0Chunk0RowCheck 0
    && tttLargeFiber50Block0Chunk0RowCheck 1
    && tttLargeFiber50Block0Chunk0RowCheck 2
    && tttLargeFiber50Block0Chunk0RowCheck 3
    && tttLargeFiber50Block0Chunk0RowCheck 4
    && tttLargeFiber50Block0Chunk0RowCheck 5
    && tttLargeFiber50Block0Chunk0RowCheck 6
    && tttLargeFiber50Block0Chunk0RowCheck 7
    && tttLargeFiber50Block0Chunk0RowCheck 8
    && tttLargeFiber50Block0Chunk0RowCheck 9
    && tttLargeFiber50Block0Chunk0RowCheck 10
    && tttLargeFiber50Block0Chunk0RowCheck 11
    && tttLargeFiber50Block0Chunk0RowCheck 12
    && tttLargeFiber50Block0Chunk0RowCheck 13
    && tttLargeFiber50Block0Chunk0RowCheck 14
    && tttLargeFiber50Block0Chunk0RowCheck 15

theorem tttLargeFiber50Block0Chunk0RowsAudit_ok :
    tttLargeFiber50Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber50Block0Chunk0RowsAudit,
    tttLargeFiber50Block0Chunk0Row_0_ok,
    tttLargeFiber50Block0Chunk0Row_1_ok,
    tttLargeFiber50Block0Chunk0Row_2_ok,
    tttLargeFiber50Block0Chunk0Row_3_ok,
    tttLargeFiber50Block0Chunk0Row_4_ok,
    tttLargeFiber50Block0Chunk0Row_5_ok,
    tttLargeFiber50Block0Chunk0Row_6_ok,
    tttLargeFiber50Block0Chunk0Row_7_ok,
    tttLargeFiber50Block0Chunk0Row_8_ok,
    tttLargeFiber50Block0Chunk0Row_9_ok,
    tttLargeFiber50Block0Chunk0Row_10_ok,
    tttLargeFiber50Block0Chunk0Row_11_ok,
    tttLargeFiber50Block0Chunk0Row_12_ok,
    tttLargeFiber50Block0Chunk0Row_13_ok,
    tttLargeFiber50Block0Chunk0Row_14_ok,
    tttLargeFiber50Block0Chunk0Row_15_ok]

def tttLargeFiber50Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber50Block0Chunk0ParentMapCheck 0
    && tttLargeFiber50Block0Chunk0ParentMapCheck 1
    && tttLargeFiber50Block0Chunk0ParentMapCheck 2
    && tttLargeFiber50Block0Chunk0ParentMapCheck 3
    && tttLargeFiber50Block0Chunk0ParentMapCheck 4
    && tttLargeFiber50Block0Chunk0ParentMapCheck 5
    && tttLargeFiber50Block0Chunk0ParentMapCheck 6
    && tttLargeFiber50Block0Chunk0ParentMapCheck 7
    && tttLargeFiber50Block0Chunk0ParentMapCheck 8
    && tttLargeFiber50Block0Chunk0ParentMapCheck 9
    && tttLargeFiber50Block0Chunk0ParentMapCheck 10
    && tttLargeFiber50Block0Chunk0ParentMapCheck 11
    && tttLargeFiber50Block0Chunk0ParentMapCheck 12
    && tttLargeFiber50Block0Chunk0ParentMapCheck 13
    && tttLargeFiber50Block0Chunk0ParentMapCheck 14
    && tttLargeFiber50Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber50Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber50Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber50Block0Chunk0ParentMapAudit,
    tttLargeFiber50Block0Chunk0ParentMap_0_ok,
    tttLargeFiber50Block0Chunk0ParentMap_1_ok,
    tttLargeFiber50Block0Chunk0ParentMap_2_ok,
    tttLargeFiber50Block0Chunk0ParentMap_3_ok,
    tttLargeFiber50Block0Chunk0ParentMap_4_ok,
    tttLargeFiber50Block0Chunk0ParentMap_5_ok,
    tttLargeFiber50Block0Chunk0ParentMap_6_ok,
    tttLargeFiber50Block0Chunk0ParentMap_7_ok,
    tttLargeFiber50Block0Chunk0ParentMap_8_ok,
    tttLargeFiber50Block0Chunk0ParentMap_9_ok,
    tttLargeFiber50Block0Chunk0ParentMap_10_ok,
    tttLargeFiber50Block0Chunk0ParentMap_11_ok,
    tttLargeFiber50Block0Chunk0ParentMap_12_ok,
    tttLargeFiber50Block0Chunk0ParentMap_13_ok,
    tttLargeFiber50Block0Chunk0ParentMap_14_ok,
    tttLargeFiber50Block0Chunk0ParentMap_15_ok]

def tttLargeFiber50Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber50Block0Chunk0ParentPathCheck 0
    && tttLargeFiber50Block0Chunk0ParentPathCheck 1
    && tttLargeFiber50Block0Chunk0ParentPathCheck 2
    && tttLargeFiber50Block0Chunk0ParentPathCheck 3
    && tttLargeFiber50Block0Chunk0ParentPathCheck 4
    && tttLargeFiber50Block0Chunk0ParentPathCheck 5
    && tttLargeFiber50Block0Chunk0ParentPathCheck 6
    && tttLargeFiber50Block0Chunk0ParentPathCheck 7
    && tttLargeFiber50Block0Chunk0ParentPathCheck 8
    && tttLargeFiber50Block0Chunk0ParentPathCheck 9
    && tttLargeFiber50Block0Chunk0ParentPathCheck 10
    && tttLargeFiber50Block0Chunk0ParentPathCheck 11
    && tttLargeFiber50Block0Chunk0ParentPathCheck 12
    && tttLargeFiber50Block0Chunk0ParentPathCheck 13
    && tttLargeFiber50Block0Chunk0ParentPathCheck 14
    && tttLargeFiber50Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber50Block0Chunk0ParentsAudit_ok :
    tttLargeFiber50Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber50Block0Chunk0ParentsAudit,
    tttLargeFiber50Block0Chunk0ParentPath_0_ok,
    tttLargeFiber50Block0Chunk0ParentPath_1_ok,
    tttLargeFiber50Block0Chunk0ParentPath_2_ok,
    tttLargeFiber50Block0Chunk0ParentPath_3_ok,
    tttLargeFiber50Block0Chunk0ParentPath_4_ok,
    tttLargeFiber50Block0Chunk0ParentPath_5_ok,
    tttLargeFiber50Block0Chunk0ParentPath_6_ok,
    tttLargeFiber50Block0Chunk0ParentPath_7_ok,
    tttLargeFiber50Block0Chunk0ParentPath_8_ok,
    tttLargeFiber50Block0Chunk0ParentPath_9_ok,
    tttLargeFiber50Block0Chunk0ParentPath_10_ok,
    tttLargeFiber50Block0Chunk0ParentPath_11_ok,
    tttLargeFiber50Block0Chunk0ParentPath_12_ok,
    tttLargeFiber50Block0Chunk0ParentPath_13_ok,
    tttLargeFiber50Block0Chunk0ParentPath_14_ok,
    tttLargeFiber50Block0Chunk0ParentPath_15_ok]

def tttLargeFiber50Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block0Chunk0SourcesCheck &&
    tttLargeFiber50Block0Chunk0RowsAudit &&
    tttLargeFiber50Block0Chunk0ParentMapAudit &&
    tttLargeFiber50Block0Chunk0ParentsAudit

theorem tttLargeFiber50Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber50Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block0Chunk0SourcesCheck_ok,
    tttLargeFiber50Block0Chunk0RowsAudit_ok,
    tttLargeFiber50Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber50Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
