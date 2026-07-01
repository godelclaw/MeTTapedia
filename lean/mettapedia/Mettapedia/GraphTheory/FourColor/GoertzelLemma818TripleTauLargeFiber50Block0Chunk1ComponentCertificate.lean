import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block0Chunk1Sources : List Nat :=
  [   5200, 5201, 5202, 5203, 5204, 5205, 5206, 5207,
   5208, 5209, 5210, 5211, 5212, 5213, 5214, 5215]

def tttLargeFiber50Row16 : TripleComponentParentRow :=
  tripleRow 5200 5204 156 150 0 156 150 48
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row17 : TripleComponentParentRow :=
  tripleRow 5201 5205 156 150 1 156 150 49
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row18 : TripleComponentParentRow :=
  tripleRow 5202 5196 156 150 2 156 149 172
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row19 : TripleComponentParentRow :=
  tripleRow 5203 5197 156 150 3 156 149 173
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row20 : TripleComponentParentRow :=
  tripleRow 5204 5192 156 150 48 156 149 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row21 : TripleComponentParentRow :=
  tripleRow 5205 5193 156 150 49 156 149 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row22 : TripleComponentParentRow :=
  tripleRow 5206 5194 156 150 50 156 149 158
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row23 : TripleComponentParentRow :=
  tripleRow 5207 5195 156 150 51 156 149 159
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row24 : TripleComponentParentRow :=
  tripleRow 5208 5212 156 151 8 156 151 56
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row25 : TripleComponentParentRow :=
  tripleRow 5209 5213 156 151 9 156 151 57
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row26 : TripleComponentParentRow :=
  tripleRow 5210 5188 156 151 10 156 148 164
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row27 : TripleComponentParentRow :=
  tripleRow 5211 5189 156 151 11 156 148 165
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row28 : TripleComponentParentRow :=
  tripleRow 5212 5184 156 151 56 156 148 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row29 : TripleComponentParentRow :=
  tripleRow 5213 5185 156 151 57 156 148 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row30 : TripleComponentParentRow :=
  tripleRow 5214 5186 156 151 58 156 148 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row31 : TripleComponentParentRow :=
  tripleRow 5215 5187 156 151 59 156 148 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row16
  , tttLargeFiber50Row17
  , tttLargeFiber50Row18
  , tttLargeFiber50Row19
  , tttLargeFiber50Row20
  , tttLargeFiber50Row21
  , tttLargeFiber50Row22
  , tttLargeFiber50Row23
  , tttLargeFiber50Row24
  , tttLargeFiber50Row25
  , tttLargeFiber50Row26
  , tttLargeFiber50Row27
  , tttLargeFiber50Row28
  , tttLargeFiber50Row29
  , tttLargeFiber50Row30
  , tttLargeFiber50Row31
  ]

def tttLargeFiber50Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber50Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber50Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber50Block0Chunk1Sources

theorem tttLargeFiber50Block0Chunk1SourcesCheck_ok :
    tttLargeFiber50Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber50Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block0Chunk1RowValid
    (listGetD tttLargeFiber50Block0Chunk1Rows i default)

def tttLargeFiber50Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block0Chunk1Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block0Chunk1Sources 0 0 == 5200
      && tttLargeFiber50ParentOf 5200 == 5204
      && tttLargeFiber50ParentOf 5204 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block0Chunk1Sources 1 0 == 5201
      && tttLargeFiber50ParentOf 5201 == 5205
      && tttLargeFiber50ParentOf 5205 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block0Chunk1Sources 2 0 == 5202
      && tttLargeFiber50ParentOf 5202 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block0Chunk1Sources 3 0 == 5203
      && tttLargeFiber50ParentOf 5203 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block0Chunk1Sources 4 0 == 5204
      && tttLargeFiber50ParentOf 5204 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block0Chunk1Sources 5 0 == 5205
      && tttLargeFiber50ParentOf 5205 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block0Chunk1Sources 6 0 == 5206
      && tttLargeFiber50ParentOf 5206 == 5194
      && tttLargeFiber50ParentOf 5194 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block0Chunk1Sources 7 0 == 5207
      && tttLargeFiber50ParentOf 5207 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block0Chunk1Sources 8 0 == 5208
      && tttLargeFiber50ParentOf 5208 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block0Chunk1Sources 9 0 == 5209
      && tttLargeFiber50ParentOf 5209 == 5213
      && tttLargeFiber50ParentOf 5213 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block0Chunk1Sources 10 0 == 5210
      && tttLargeFiber50ParentOf 5210 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block0Chunk1Sources 11 0 == 5211
      && tttLargeFiber50ParentOf 5211 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block0Chunk1Sources 12 0 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (1 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block0Chunk1Sources 13 0 == 5213
      && tttLargeFiber50ParentOf 5213 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block0Chunk1Sources 14 0 == 5214
      && tttLargeFiber50ParentOf 5214 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block0Chunk1Sources 15 0 == 5215
      && tttLargeFiber50ParentOf 5215 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block0Chunk1Row_0_ok :
    tttLargeFiber50Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_1_ok :
    tttLargeFiber50Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_2_ok :
    tttLargeFiber50Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_3_ok :
    tttLargeFiber50Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_4_ok :
    tttLargeFiber50Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_5_ok :
    tttLargeFiber50Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_6_ok :
    tttLargeFiber50Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_7_ok :
    tttLargeFiber50Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_8_ok :
    tttLargeFiber50Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_9_ok :
    tttLargeFiber50Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_10_ok :
    tttLargeFiber50Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_11_ok :
    tttLargeFiber50Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_12_ok :
    tttLargeFiber50Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_13_ok :
    tttLargeFiber50Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_14_ok :
    tttLargeFiber50Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1Row_15_ok :
    tttLargeFiber50Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_0_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_1_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_2_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_3_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_4_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_5_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_6_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_7_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_8_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_9_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_10_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_11_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_12_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_13_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_14_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentMap_15_ok :
    tttLargeFiber50Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_0_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_1_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_2_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_3_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_4_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_5_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_6_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_7_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_8_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_9_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_10_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_11_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_12_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_13_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_14_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block0Chunk1ParentPath_15_ok :
    tttLargeFiber50Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber50Block0Chunk1RowCheck 0
    && tttLargeFiber50Block0Chunk1RowCheck 1
    && tttLargeFiber50Block0Chunk1RowCheck 2
    && tttLargeFiber50Block0Chunk1RowCheck 3
    && tttLargeFiber50Block0Chunk1RowCheck 4
    && tttLargeFiber50Block0Chunk1RowCheck 5
    && tttLargeFiber50Block0Chunk1RowCheck 6
    && tttLargeFiber50Block0Chunk1RowCheck 7
    && tttLargeFiber50Block0Chunk1RowCheck 8
    && tttLargeFiber50Block0Chunk1RowCheck 9
    && tttLargeFiber50Block0Chunk1RowCheck 10
    && tttLargeFiber50Block0Chunk1RowCheck 11
    && tttLargeFiber50Block0Chunk1RowCheck 12
    && tttLargeFiber50Block0Chunk1RowCheck 13
    && tttLargeFiber50Block0Chunk1RowCheck 14
    && tttLargeFiber50Block0Chunk1RowCheck 15

theorem tttLargeFiber50Block0Chunk1RowsAudit_ok :
    tttLargeFiber50Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber50Block0Chunk1RowsAudit,
    tttLargeFiber50Block0Chunk1Row_0_ok,
    tttLargeFiber50Block0Chunk1Row_1_ok,
    tttLargeFiber50Block0Chunk1Row_2_ok,
    tttLargeFiber50Block0Chunk1Row_3_ok,
    tttLargeFiber50Block0Chunk1Row_4_ok,
    tttLargeFiber50Block0Chunk1Row_5_ok,
    tttLargeFiber50Block0Chunk1Row_6_ok,
    tttLargeFiber50Block0Chunk1Row_7_ok,
    tttLargeFiber50Block0Chunk1Row_8_ok,
    tttLargeFiber50Block0Chunk1Row_9_ok,
    tttLargeFiber50Block0Chunk1Row_10_ok,
    tttLargeFiber50Block0Chunk1Row_11_ok,
    tttLargeFiber50Block0Chunk1Row_12_ok,
    tttLargeFiber50Block0Chunk1Row_13_ok,
    tttLargeFiber50Block0Chunk1Row_14_ok,
    tttLargeFiber50Block0Chunk1Row_15_ok]

def tttLargeFiber50Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber50Block0Chunk1ParentMapCheck 0
    && tttLargeFiber50Block0Chunk1ParentMapCheck 1
    && tttLargeFiber50Block0Chunk1ParentMapCheck 2
    && tttLargeFiber50Block0Chunk1ParentMapCheck 3
    && tttLargeFiber50Block0Chunk1ParentMapCheck 4
    && tttLargeFiber50Block0Chunk1ParentMapCheck 5
    && tttLargeFiber50Block0Chunk1ParentMapCheck 6
    && tttLargeFiber50Block0Chunk1ParentMapCheck 7
    && tttLargeFiber50Block0Chunk1ParentMapCheck 8
    && tttLargeFiber50Block0Chunk1ParentMapCheck 9
    && tttLargeFiber50Block0Chunk1ParentMapCheck 10
    && tttLargeFiber50Block0Chunk1ParentMapCheck 11
    && tttLargeFiber50Block0Chunk1ParentMapCheck 12
    && tttLargeFiber50Block0Chunk1ParentMapCheck 13
    && tttLargeFiber50Block0Chunk1ParentMapCheck 14
    && tttLargeFiber50Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber50Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber50Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber50Block0Chunk1ParentMapAudit,
    tttLargeFiber50Block0Chunk1ParentMap_0_ok,
    tttLargeFiber50Block0Chunk1ParentMap_1_ok,
    tttLargeFiber50Block0Chunk1ParentMap_2_ok,
    tttLargeFiber50Block0Chunk1ParentMap_3_ok,
    tttLargeFiber50Block0Chunk1ParentMap_4_ok,
    tttLargeFiber50Block0Chunk1ParentMap_5_ok,
    tttLargeFiber50Block0Chunk1ParentMap_6_ok,
    tttLargeFiber50Block0Chunk1ParentMap_7_ok,
    tttLargeFiber50Block0Chunk1ParentMap_8_ok,
    tttLargeFiber50Block0Chunk1ParentMap_9_ok,
    tttLargeFiber50Block0Chunk1ParentMap_10_ok,
    tttLargeFiber50Block0Chunk1ParentMap_11_ok,
    tttLargeFiber50Block0Chunk1ParentMap_12_ok,
    tttLargeFiber50Block0Chunk1ParentMap_13_ok,
    tttLargeFiber50Block0Chunk1ParentMap_14_ok,
    tttLargeFiber50Block0Chunk1ParentMap_15_ok]

def tttLargeFiber50Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber50Block0Chunk1ParentPathCheck 0
    && tttLargeFiber50Block0Chunk1ParentPathCheck 1
    && tttLargeFiber50Block0Chunk1ParentPathCheck 2
    && tttLargeFiber50Block0Chunk1ParentPathCheck 3
    && tttLargeFiber50Block0Chunk1ParentPathCheck 4
    && tttLargeFiber50Block0Chunk1ParentPathCheck 5
    && tttLargeFiber50Block0Chunk1ParentPathCheck 6
    && tttLargeFiber50Block0Chunk1ParentPathCheck 7
    && tttLargeFiber50Block0Chunk1ParentPathCheck 8
    && tttLargeFiber50Block0Chunk1ParentPathCheck 9
    && tttLargeFiber50Block0Chunk1ParentPathCheck 10
    && tttLargeFiber50Block0Chunk1ParentPathCheck 11
    && tttLargeFiber50Block0Chunk1ParentPathCheck 12
    && tttLargeFiber50Block0Chunk1ParentPathCheck 13
    && tttLargeFiber50Block0Chunk1ParentPathCheck 14
    && tttLargeFiber50Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber50Block0Chunk1ParentsAudit_ok :
    tttLargeFiber50Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber50Block0Chunk1ParentsAudit,
    tttLargeFiber50Block0Chunk1ParentPath_0_ok,
    tttLargeFiber50Block0Chunk1ParentPath_1_ok,
    tttLargeFiber50Block0Chunk1ParentPath_2_ok,
    tttLargeFiber50Block0Chunk1ParentPath_3_ok,
    tttLargeFiber50Block0Chunk1ParentPath_4_ok,
    tttLargeFiber50Block0Chunk1ParentPath_5_ok,
    tttLargeFiber50Block0Chunk1ParentPath_6_ok,
    tttLargeFiber50Block0Chunk1ParentPath_7_ok,
    tttLargeFiber50Block0Chunk1ParentPath_8_ok,
    tttLargeFiber50Block0Chunk1ParentPath_9_ok,
    tttLargeFiber50Block0Chunk1ParentPath_10_ok,
    tttLargeFiber50Block0Chunk1ParentPath_11_ok,
    tttLargeFiber50Block0Chunk1ParentPath_12_ok,
    tttLargeFiber50Block0Chunk1ParentPath_13_ok,
    tttLargeFiber50Block0Chunk1ParentPath_14_ok,
    tttLargeFiber50Block0Chunk1ParentPath_15_ok]

def tttLargeFiber50Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block0Chunk1SourcesCheck &&
    tttLargeFiber50Block0Chunk1RowsAudit &&
    tttLargeFiber50Block0Chunk1ParentMapAudit &&
    tttLargeFiber50Block0Chunk1ParentsAudit

theorem tttLargeFiber50Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber50Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block0Chunk1SourcesCheck_ok,
    tttLargeFiber50Block0Chunk1RowsAudit_ok,
    tttLargeFiber50Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber50Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
