import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 3 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block3Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block3Chunk1Sources : List Nat :=
  [   5392, 5393, 5394, 5395, 5396, 5397, 5398, 5399,
   5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407]

def tttLargeFiber50Row208 : TripleComponentParentRow :=
  tripleRow 5392 5396 159 10 16 159 10 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row209 : TripleComponentParentRow :=
  tripleRow 5393 5397 159 10 17 159 10 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row210 : TripleComponentParentRow :=
  tripleRow 5394 5220 159 10 18 156 164 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber50Row211 : TripleComponentParentRow :=
  tripleRow 5395 5221 159 10 19 156 164 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber50Row212 : TripleComponentParentRow :=
  tripleRow 5396 5216 159 10 32 156 164 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row213 : TripleComponentParentRow :=
  tripleRow 5397 5217 159 10 33 156 164 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row214 : TripleComponentParentRow :=
  tripleRow 5398 5218 159 10 34 156 164 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row215 : TripleComponentParentRow :=
  tripleRow 5399 5219 159 10 35 156 164 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row216 : TripleComponentParentRow :=
  tripleRow 5400 5404 159 11 24 159 11 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row217 : TripleComponentParentRow :=
  tripleRow 5401 5405 159 11 25 159 11 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row218 : TripleComponentParentRow :=
  tripleRow 5402 5228 159 11 26 156 165 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber50Row219 : TripleComponentParentRow :=
  tripleRow 5403 5229 159 11 27 156 165 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber50Row220 : TripleComponentParentRow :=
  tripleRow 5404 5224 159 11 40 156 165 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row221 : TripleComponentParentRow :=
  tripleRow 5405 5225 159 11 41 156 165 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row222 : TripleComponentParentRow :=
  tripleRow 5406 5226 159 11 42 156 165 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row223 : TripleComponentParentRow :=
  tripleRow 5407 5227 159 11 43 156 165 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Block3Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row208
  , tttLargeFiber50Row209
  , tttLargeFiber50Row210
  , tttLargeFiber50Row211
  , tttLargeFiber50Row212
  , tttLargeFiber50Row213
  , tttLargeFiber50Row214
  , tttLargeFiber50Row215
  , tttLargeFiber50Row216
  , tttLargeFiber50Row217
  , tttLargeFiber50Row218
  , tttLargeFiber50Row219
  , tttLargeFiber50Row220
  , tttLargeFiber50Row221
  , tttLargeFiber50Row222
  , tttLargeFiber50Row223
  ]

def tttLargeFiber50Block3Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block3Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block3Chunk1ExpectedContains row.source &&
    tttLargeFiber50Block3Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block3Chunk1SourcesCheck : Bool :=
  (tttLargeFiber50Block3Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber50Block3Chunk1Sources

theorem tttLargeFiber50Block3Chunk1SourcesCheck_ok :
    tttLargeFiber50Block3Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber50Block3Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block3Chunk1RowValid
    (listGetD tttLargeFiber50Block3Chunk1Rows i default)

def tttLargeFiber50Block3Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block3Chunk1Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block3Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block3Chunk1Sources 0 0 == 5392
      && tttLargeFiber50ParentOf 5392 == 5396
      && tttLargeFiber50ParentOf 5396 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block3Chunk1Sources 1 0 == 5393
      && tttLargeFiber50ParentOf 5393 == 5397
      && tttLargeFiber50ParentOf 5397 == 5217
      && tttLargeFiber50ParentOf 5217 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block3Chunk1Sources 2 0 == 5394
      && tttLargeFiber50ParentOf 5394 == 5220
      && tttLargeFiber50ParentOf 5220 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block3Chunk1Sources 3 0 == 5395
      && tttLargeFiber50ParentOf 5395 == 5221
      && tttLargeFiber50ParentOf 5221 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block3Chunk1Sources 4 0 == 5396
      && tttLargeFiber50ParentOf 5396 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block3Chunk1Sources 5 0 == 5397
      && tttLargeFiber50ParentOf 5397 == 5217
      && tttLargeFiber50ParentOf 5217 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block3Chunk1Sources 6 0 == 5398
      && tttLargeFiber50ParentOf 5398 == 5218
      && tttLargeFiber50ParentOf 5218 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block3Chunk1Sources 7 0 == 5399
      && tttLargeFiber50ParentOf 5399 == 5219
      && tttLargeFiber50ParentOf 5219 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block3Chunk1Sources 8 0 == 5400
      && tttLargeFiber50ParentOf 5400 == 5404
      && tttLargeFiber50ParentOf 5404 == 5224
      && tttLargeFiber50ParentOf 5224 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block3Chunk1Sources 9 0 == 5401
      && tttLargeFiber50ParentOf 5401 == 5405
      && tttLargeFiber50ParentOf 5405 == 5225
      && tttLargeFiber50ParentOf 5225 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block3Chunk1Sources 10 0 == 5402
      && tttLargeFiber50ParentOf 5402 == 5228
      && tttLargeFiber50ParentOf 5228 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block3Chunk1Sources 11 0 == 5403
      && tttLargeFiber50ParentOf 5403 == 5229
      && tttLargeFiber50ParentOf 5229 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block3Chunk1Sources 12 0 == 5404
      && tttLargeFiber50ParentOf 5404 == 5224
      && tttLargeFiber50ParentOf 5224 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block3Chunk1Sources 13 0 == 5405
      && tttLargeFiber50ParentOf 5405 == 5225
      && tttLargeFiber50ParentOf 5225 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block3Chunk1Sources 14 0 == 5406
      && tttLargeFiber50ParentOf 5406 == 5226
      && tttLargeFiber50ParentOf 5226 == 5194
      && tttLargeFiber50ParentOf 5194 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block3Chunk1Sources 15 0 == 5407
      && tttLargeFiber50ParentOf 5407 == 5227
      && tttLargeFiber50ParentOf 5227 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block3Chunk1Row_0_ok :
    tttLargeFiber50Block3Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_1_ok :
    tttLargeFiber50Block3Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_2_ok :
    tttLargeFiber50Block3Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_3_ok :
    tttLargeFiber50Block3Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_4_ok :
    tttLargeFiber50Block3Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_5_ok :
    tttLargeFiber50Block3Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_6_ok :
    tttLargeFiber50Block3Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_7_ok :
    tttLargeFiber50Block3Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_8_ok :
    tttLargeFiber50Block3Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_9_ok :
    tttLargeFiber50Block3Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_10_ok :
    tttLargeFiber50Block3Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_11_ok :
    tttLargeFiber50Block3Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_12_ok :
    tttLargeFiber50Block3Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_13_ok :
    tttLargeFiber50Block3Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_14_ok :
    tttLargeFiber50Block3Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1Row_15_ok :
    tttLargeFiber50Block3Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_0_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_1_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_2_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_3_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_4_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_5_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_6_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_7_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_8_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_9_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_10_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_11_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_12_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_13_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_14_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentMap_15_ok :
    tttLargeFiber50Block3Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_0_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_1_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_2_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_3_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_4_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_5_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_6_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_7_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_8_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_9_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_10_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_11_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_12_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_13_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_14_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block3Chunk1ParentPath_15_ok :
    tttLargeFiber50Block3Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block3Chunk1RowsAudit : Bool :=
  tttLargeFiber50Block3Chunk1RowCheck 0
    && tttLargeFiber50Block3Chunk1RowCheck 1
    && tttLargeFiber50Block3Chunk1RowCheck 2
    && tttLargeFiber50Block3Chunk1RowCheck 3
    && tttLargeFiber50Block3Chunk1RowCheck 4
    && tttLargeFiber50Block3Chunk1RowCheck 5
    && tttLargeFiber50Block3Chunk1RowCheck 6
    && tttLargeFiber50Block3Chunk1RowCheck 7
    && tttLargeFiber50Block3Chunk1RowCheck 8
    && tttLargeFiber50Block3Chunk1RowCheck 9
    && tttLargeFiber50Block3Chunk1RowCheck 10
    && tttLargeFiber50Block3Chunk1RowCheck 11
    && tttLargeFiber50Block3Chunk1RowCheck 12
    && tttLargeFiber50Block3Chunk1RowCheck 13
    && tttLargeFiber50Block3Chunk1RowCheck 14
    && tttLargeFiber50Block3Chunk1RowCheck 15

theorem tttLargeFiber50Block3Chunk1RowsAudit_ok :
    tttLargeFiber50Block3Chunk1RowsAudit = true := by
  simp [tttLargeFiber50Block3Chunk1RowsAudit,
    tttLargeFiber50Block3Chunk1Row_0_ok,
    tttLargeFiber50Block3Chunk1Row_1_ok,
    tttLargeFiber50Block3Chunk1Row_2_ok,
    tttLargeFiber50Block3Chunk1Row_3_ok,
    tttLargeFiber50Block3Chunk1Row_4_ok,
    tttLargeFiber50Block3Chunk1Row_5_ok,
    tttLargeFiber50Block3Chunk1Row_6_ok,
    tttLargeFiber50Block3Chunk1Row_7_ok,
    tttLargeFiber50Block3Chunk1Row_8_ok,
    tttLargeFiber50Block3Chunk1Row_9_ok,
    tttLargeFiber50Block3Chunk1Row_10_ok,
    tttLargeFiber50Block3Chunk1Row_11_ok,
    tttLargeFiber50Block3Chunk1Row_12_ok,
    tttLargeFiber50Block3Chunk1Row_13_ok,
    tttLargeFiber50Block3Chunk1Row_14_ok,
    tttLargeFiber50Block3Chunk1Row_15_ok]

def tttLargeFiber50Block3Chunk1ParentMapAudit : Bool :=
  tttLargeFiber50Block3Chunk1ParentMapCheck 0
    && tttLargeFiber50Block3Chunk1ParentMapCheck 1
    && tttLargeFiber50Block3Chunk1ParentMapCheck 2
    && tttLargeFiber50Block3Chunk1ParentMapCheck 3
    && tttLargeFiber50Block3Chunk1ParentMapCheck 4
    && tttLargeFiber50Block3Chunk1ParentMapCheck 5
    && tttLargeFiber50Block3Chunk1ParentMapCheck 6
    && tttLargeFiber50Block3Chunk1ParentMapCheck 7
    && tttLargeFiber50Block3Chunk1ParentMapCheck 8
    && tttLargeFiber50Block3Chunk1ParentMapCheck 9
    && tttLargeFiber50Block3Chunk1ParentMapCheck 10
    && tttLargeFiber50Block3Chunk1ParentMapCheck 11
    && tttLargeFiber50Block3Chunk1ParentMapCheck 12
    && tttLargeFiber50Block3Chunk1ParentMapCheck 13
    && tttLargeFiber50Block3Chunk1ParentMapCheck 14
    && tttLargeFiber50Block3Chunk1ParentMapCheck 15

theorem tttLargeFiber50Block3Chunk1ParentMapAudit_ok :
    tttLargeFiber50Block3Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber50Block3Chunk1ParentMapAudit,
    tttLargeFiber50Block3Chunk1ParentMap_0_ok,
    tttLargeFiber50Block3Chunk1ParentMap_1_ok,
    tttLargeFiber50Block3Chunk1ParentMap_2_ok,
    tttLargeFiber50Block3Chunk1ParentMap_3_ok,
    tttLargeFiber50Block3Chunk1ParentMap_4_ok,
    tttLargeFiber50Block3Chunk1ParentMap_5_ok,
    tttLargeFiber50Block3Chunk1ParentMap_6_ok,
    tttLargeFiber50Block3Chunk1ParentMap_7_ok,
    tttLargeFiber50Block3Chunk1ParentMap_8_ok,
    tttLargeFiber50Block3Chunk1ParentMap_9_ok,
    tttLargeFiber50Block3Chunk1ParentMap_10_ok,
    tttLargeFiber50Block3Chunk1ParentMap_11_ok,
    tttLargeFiber50Block3Chunk1ParentMap_12_ok,
    tttLargeFiber50Block3Chunk1ParentMap_13_ok,
    tttLargeFiber50Block3Chunk1ParentMap_14_ok,
    tttLargeFiber50Block3Chunk1ParentMap_15_ok]

def tttLargeFiber50Block3Chunk1ParentsAudit : Bool :=
  tttLargeFiber50Block3Chunk1ParentPathCheck 0
    && tttLargeFiber50Block3Chunk1ParentPathCheck 1
    && tttLargeFiber50Block3Chunk1ParentPathCheck 2
    && tttLargeFiber50Block3Chunk1ParentPathCheck 3
    && tttLargeFiber50Block3Chunk1ParentPathCheck 4
    && tttLargeFiber50Block3Chunk1ParentPathCheck 5
    && tttLargeFiber50Block3Chunk1ParentPathCheck 6
    && tttLargeFiber50Block3Chunk1ParentPathCheck 7
    && tttLargeFiber50Block3Chunk1ParentPathCheck 8
    && tttLargeFiber50Block3Chunk1ParentPathCheck 9
    && tttLargeFiber50Block3Chunk1ParentPathCheck 10
    && tttLargeFiber50Block3Chunk1ParentPathCheck 11
    && tttLargeFiber50Block3Chunk1ParentPathCheck 12
    && tttLargeFiber50Block3Chunk1ParentPathCheck 13
    && tttLargeFiber50Block3Chunk1ParentPathCheck 14
    && tttLargeFiber50Block3Chunk1ParentPathCheck 15

theorem tttLargeFiber50Block3Chunk1ParentsAudit_ok :
    tttLargeFiber50Block3Chunk1ParentsAudit = true := by
  simp [tttLargeFiber50Block3Chunk1ParentsAudit,
    tttLargeFiber50Block3Chunk1ParentPath_0_ok,
    tttLargeFiber50Block3Chunk1ParentPath_1_ok,
    tttLargeFiber50Block3Chunk1ParentPath_2_ok,
    tttLargeFiber50Block3Chunk1ParentPath_3_ok,
    tttLargeFiber50Block3Chunk1ParentPath_4_ok,
    tttLargeFiber50Block3Chunk1ParentPath_5_ok,
    tttLargeFiber50Block3Chunk1ParentPath_6_ok,
    tttLargeFiber50Block3Chunk1ParentPath_7_ok,
    tttLargeFiber50Block3Chunk1ParentPath_8_ok,
    tttLargeFiber50Block3Chunk1ParentPath_9_ok,
    tttLargeFiber50Block3Chunk1ParentPath_10_ok,
    tttLargeFiber50Block3Chunk1ParentPath_11_ok,
    tttLargeFiber50Block3Chunk1ParentPath_12_ok,
    tttLargeFiber50Block3Chunk1ParentPath_13_ok,
    tttLargeFiber50Block3Chunk1ParentPath_14_ok,
    tttLargeFiber50Block3Chunk1ParentPath_15_ok]

def tttLargeFiber50Block3Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block3Chunk1SourcesCheck &&
    tttLargeFiber50Block3Chunk1RowsAudit &&
    tttLargeFiber50Block3Chunk1ParentMapAudit &&
    tttLargeFiber50Block3Chunk1ParentsAudit

theorem tttLargeFiber50Block3Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber50Block3Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block3Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block3Chunk1SourcesCheck_ok,
    tttLargeFiber50Block3Chunk1RowsAudit_ok,
    tttLargeFiber50Block3Chunk1ParentMapAudit_ok,
    tttLargeFiber50Block3Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block3Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
