import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 3 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block3Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block3Chunk0Sources : List Nat :=
  [   5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383,
   5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391]

def tttLargeFiber50Row192 : TripleComponentParentRow :=
  tripleRow 5376 5408 159 8 80 159 56 148
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

def tttLargeFiber50Row193 : TripleComponentParentRow :=
  tripleRow 5377 5409 159 8 81 159 56 149
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

def tttLargeFiber50Row194 : TripleComponentParentRow :=
  tripleRow 5378 5376 159 8 82 159 8 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row195 : TripleComponentParentRow :=
  tripleRow 5379 5411 159 8 83 159 56 151
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row196 : TripleComponentParentRow :=
  tripleRow 5380 5412 159 8 100 159 56 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row197 : TripleComponentParentRow :=
  tripleRow 5381 5413 159 8 101 159 56 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row198 : TripleComponentParentRow :=
  tripleRow 5382 5377 159 8 102 159 8 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row199 : TripleComponentParentRow :=
  tripleRow 5383 5376 159 8 103 159 8 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Row200 : TripleComponentParentRow :=
  tripleRow 5384 5416 159 9 88 159 57 156
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

def tttLargeFiber50Row201 : TripleComponentParentRow :=
  tripleRow 5385 5417 159 9 89 159 57 157
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

def tttLargeFiber50Row202 : TripleComponentParentRow :=
  tripleRow 5386 5384 159 9 90 159 9 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row203 : TripleComponentParentRow :=
  tripleRow 5387 5419 159 9 91 159 57 159
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row204 : TripleComponentParentRow :=
  tripleRow 5388 5420 159 9 108 159 57 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row205 : TripleComponentParentRow :=
  tripleRow 5389 5421 159 9 109 159 57 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row206 : TripleComponentParentRow :=
  tripleRow 5390 5385 159 9 110 159 9 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row207 : TripleComponentParentRow :=
  tripleRow 5391 5384 159 9 111 159 9 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Block3Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row192
  , tttLargeFiber50Row193
  , tttLargeFiber50Row194
  , tttLargeFiber50Row195
  , tttLargeFiber50Row196
  , tttLargeFiber50Row197
  , tttLargeFiber50Row198
  , tttLargeFiber50Row199
  , tttLargeFiber50Row200
  , tttLargeFiber50Row201
  , tttLargeFiber50Row202
  , tttLargeFiber50Row203
  , tttLargeFiber50Row204
  , tttLargeFiber50Row205
  , tttLargeFiber50Row206
  , tttLargeFiber50Row207
  ]

def tttLargeFiber50Block3Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block3Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block3Chunk0ExpectedContains row.source &&
    tttLargeFiber50Block3Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block3Chunk0SourcesCheck : Bool :=
  (tttLargeFiber50Block3Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber50Block3Chunk0Sources

theorem tttLargeFiber50Block3Chunk0SourcesCheck_ok :
    tttLargeFiber50Block3Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber50Block3Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block3Chunk0RowValid
    (listGetD tttLargeFiber50Block3Chunk0Rows i default)

def tttLargeFiber50Block3Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block3Chunk0Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block3Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block3Chunk0Sources 0 0 == 5376
      && tttLargeFiber50ParentOf 5376 == 5408
      && tttLargeFiber50ParentOf 5408 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block3Chunk0Sources 1 0 == 5377
      && tttLargeFiber50ParentOf 5377 == 5409
      && tttLargeFiber50ParentOf 5409 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block3Chunk0Sources 2 0 == 5378
      && tttLargeFiber50ParentOf 5378 == 5376
      && tttLargeFiber50ParentOf 5376 == 5408
      && tttLargeFiber50ParentOf 5408 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block3Chunk0Sources 3 0 == 5379
      && tttLargeFiber50ParentOf 5379 == 5411
      && tttLargeFiber50ParentOf 5411 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block3Chunk0Sources 4 0 == 5380
      && tttLargeFiber50ParentOf 5380 == 5412
      && tttLargeFiber50ParentOf 5412 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block3Chunk0Sources 5 0 == 5381
      && tttLargeFiber50ParentOf 5381 == 5413
      && tttLargeFiber50ParentOf 5413 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block3Chunk0Sources 6 0 == 5382
      && tttLargeFiber50ParentOf 5382 == 5377
      && tttLargeFiber50ParentOf 5377 == 5409
      && tttLargeFiber50ParentOf 5409 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block3Chunk0Sources 7 0 == 5383
      && tttLargeFiber50ParentOf 5383 == 5376
      && tttLargeFiber50ParentOf 5376 == 5408
      && tttLargeFiber50ParentOf 5408 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block3Chunk0Sources 8 0 == 5384
      && tttLargeFiber50ParentOf 5384 == 5416
      && tttLargeFiber50ParentOf 5416 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block3Chunk0Sources 9 0 == 5385
      && tttLargeFiber50ParentOf 5385 == 5417
      && tttLargeFiber50ParentOf 5417 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block3Chunk0Sources 10 0 == 5386
      && tttLargeFiber50ParentOf 5386 == 5384
      && tttLargeFiber50ParentOf 5384 == 5416
      && tttLargeFiber50ParentOf 5416 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block3Chunk0Sources 11 0 == 5387
      && tttLargeFiber50ParentOf 5387 == 5419
      && tttLargeFiber50ParentOf 5419 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block3Chunk0Sources 12 0 == 5388
      && tttLargeFiber50ParentOf 5388 == 5420
      && tttLargeFiber50ParentOf 5420 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block3Chunk0Sources 13 0 == 5389
      && tttLargeFiber50ParentOf 5389 == 5421
      && tttLargeFiber50ParentOf 5421 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block3Chunk0Sources 14 0 == 5390
      && tttLargeFiber50ParentOf 5390 == 5385
      && tttLargeFiber50ParentOf 5385 == 5417
      && tttLargeFiber50ParentOf 5417 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block3Chunk0Sources 15 0 == 5391
      && tttLargeFiber50ParentOf 5391 == 5384
      && tttLargeFiber50ParentOf 5384 == 5416
      && tttLargeFiber50ParentOf 5416 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block3Chunk0Row_0_ok :
    tttLargeFiber50Block3Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_1_ok :
    tttLargeFiber50Block3Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_2_ok :
    tttLargeFiber50Block3Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_3_ok :
    tttLargeFiber50Block3Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_4_ok :
    tttLargeFiber50Block3Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_5_ok :
    tttLargeFiber50Block3Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_6_ok :
    tttLargeFiber50Block3Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_7_ok :
    tttLargeFiber50Block3Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_8_ok :
    tttLargeFiber50Block3Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_9_ok :
    tttLargeFiber50Block3Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_10_ok :
    tttLargeFiber50Block3Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_11_ok :
    tttLargeFiber50Block3Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_12_ok :
    tttLargeFiber50Block3Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_13_ok :
    tttLargeFiber50Block3Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_14_ok :
    tttLargeFiber50Block3Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0Row_15_ok :
    tttLargeFiber50Block3Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_0_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_1_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_2_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_3_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_4_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_5_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_6_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_7_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_8_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_9_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_10_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_11_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_12_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_13_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_14_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentMap_15_ok :
    tttLargeFiber50Block3Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_0_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_1_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_2_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_3_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_4_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_5_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_6_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_7_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_8_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_9_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_10_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_11_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_12_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_13_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_14_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block3Chunk0ParentPath_15_ok :
    tttLargeFiber50Block3Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block3Chunk0RowsAudit : Bool :=
  tttLargeFiber50Block3Chunk0RowCheck 0
    && tttLargeFiber50Block3Chunk0RowCheck 1
    && tttLargeFiber50Block3Chunk0RowCheck 2
    && tttLargeFiber50Block3Chunk0RowCheck 3
    && tttLargeFiber50Block3Chunk0RowCheck 4
    && tttLargeFiber50Block3Chunk0RowCheck 5
    && tttLargeFiber50Block3Chunk0RowCheck 6
    && tttLargeFiber50Block3Chunk0RowCheck 7
    && tttLargeFiber50Block3Chunk0RowCheck 8
    && tttLargeFiber50Block3Chunk0RowCheck 9
    && tttLargeFiber50Block3Chunk0RowCheck 10
    && tttLargeFiber50Block3Chunk0RowCheck 11
    && tttLargeFiber50Block3Chunk0RowCheck 12
    && tttLargeFiber50Block3Chunk0RowCheck 13
    && tttLargeFiber50Block3Chunk0RowCheck 14
    && tttLargeFiber50Block3Chunk0RowCheck 15

theorem tttLargeFiber50Block3Chunk0RowsAudit_ok :
    tttLargeFiber50Block3Chunk0RowsAudit = true := by
  simp [tttLargeFiber50Block3Chunk0RowsAudit,
    tttLargeFiber50Block3Chunk0Row_0_ok,
    tttLargeFiber50Block3Chunk0Row_1_ok,
    tttLargeFiber50Block3Chunk0Row_2_ok,
    tttLargeFiber50Block3Chunk0Row_3_ok,
    tttLargeFiber50Block3Chunk0Row_4_ok,
    tttLargeFiber50Block3Chunk0Row_5_ok,
    tttLargeFiber50Block3Chunk0Row_6_ok,
    tttLargeFiber50Block3Chunk0Row_7_ok,
    tttLargeFiber50Block3Chunk0Row_8_ok,
    tttLargeFiber50Block3Chunk0Row_9_ok,
    tttLargeFiber50Block3Chunk0Row_10_ok,
    tttLargeFiber50Block3Chunk0Row_11_ok,
    tttLargeFiber50Block3Chunk0Row_12_ok,
    tttLargeFiber50Block3Chunk0Row_13_ok,
    tttLargeFiber50Block3Chunk0Row_14_ok,
    tttLargeFiber50Block3Chunk0Row_15_ok]

def tttLargeFiber50Block3Chunk0ParentMapAudit : Bool :=
  tttLargeFiber50Block3Chunk0ParentMapCheck 0
    && tttLargeFiber50Block3Chunk0ParentMapCheck 1
    && tttLargeFiber50Block3Chunk0ParentMapCheck 2
    && tttLargeFiber50Block3Chunk0ParentMapCheck 3
    && tttLargeFiber50Block3Chunk0ParentMapCheck 4
    && tttLargeFiber50Block3Chunk0ParentMapCheck 5
    && tttLargeFiber50Block3Chunk0ParentMapCheck 6
    && tttLargeFiber50Block3Chunk0ParentMapCheck 7
    && tttLargeFiber50Block3Chunk0ParentMapCheck 8
    && tttLargeFiber50Block3Chunk0ParentMapCheck 9
    && tttLargeFiber50Block3Chunk0ParentMapCheck 10
    && tttLargeFiber50Block3Chunk0ParentMapCheck 11
    && tttLargeFiber50Block3Chunk0ParentMapCheck 12
    && tttLargeFiber50Block3Chunk0ParentMapCheck 13
    && tttLargeFiber50Block3Chunk0ParentMapCheck 14
    && tttLargeFiber50Block3Chunk0ParentMapCheck 15

theorem tttLargeFiber50Block3Chunk0ParentMapAudit_ok :
    tttLargeFiber50Block3Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber50Block3Chunk0ParentMapAudit,
    tttLargeFiber50Block3Chunk0ParentMap_0_ok,
    tttLargeFiber50Block3Chunk0ParentMap_1_ok,
    tttLargeFiber50Block3Chunk0ParentMap_2_ok,
    tttLargeFiber50Block3Chunk0ParentMap_3_ok,
    tttLargeFiber50Block3Chunk0ParentMap_4_ok,
    tttLargeFiber50Block3Chunk0ParentMap_5_ok,
    tttLargeFiber50Block3Chunk0ParentMap_6_ok,
    tttLargeFiber50Block3Chunk0ParentMap_7_ok,
    tttLargeFiber50Block3Chunk0ParentMap_8_ok,
    tttLargeFiber50Block3Chunk0ParentMap_9_ok,
    tttLargeFiber50Block3Chunk0ParentMap_10_ok,
    tttLargeFiber50Block3Chunk0ParentMap_11_ok,
    tttLargeFiber50Block3Chunk0ParentMap_12_ok,
    tttLargeFiber50Block3Chunk0ParentMap_13_ok,
    tttLargeFiber50Block3Chunk0ParentMap_14_ok,
    tttLargeFiber50Block3Chunk0ParentMap_15_ok]

def tttLargeFiber50Block3Chunk0ParentsAudit : Bool :=
  tttLargeFiber50Block3Chunk0ParentPathCheck 0
    && tttLargeFiber50Block3Chunk0ParentPathCheck 1
    && tttLargeFiber50Block3Chunk0ParentPathCheck 2
    && tttLargeFiber50Block3Chunk0ParentPathCheck 3
    && tttLargeFiber50Block3Chunk0ParentPathCheck 4
    && tttLargeFiber50Block3Chunk0ParentPathCheck 5
    && tttLargeFiber50Block3Chunk0ParentPathCheck 6
    && tttLargeFiber50Block3Chunk0ParentPathCheck 7
    && tttLargeFiber50Block3Chunk0ParentPathCheck 8
    && tttLargeFiber50Block3Chunk0ParentPathCheck 9
    && tttLargeFiber50Block3Chunk0ParentPathCheck 10
    && tttLargeFiber50Block3Chunk0ParentPathCheck 11
    && tttLargeFiber50Block3Chunk0ParentPathCheck 12
    && tttLargeFiber50Block3Chunk0ParentPathCheck 13
    && tttLargeFiber50Block3Chunk0ParentPathCheck 14
    && tttLargeFiber50Block3Chunk0ParentPathCheck 15

theorem tttLargeFiber50Block3Chunk0ParentsAudit_ok :
    tttLargeFiber50Block3Chunk0ParentsAudit = true := by
  simp [tttLargeFiber50Block3Chunk0ParentsAudit,
    tttLargeFiber50Block3Chunk0ParentPath_0_ok,
    tttLargeFiber50Block3Chunk0ParentPath_1_ok,
    tttLargeFiber50Block3Chunk0ParentPath_2_ok,
    tttLargeFiber50Block3Chunk0ParentPath_3_ok,
    tttLargeFiber50Block3Chunk0ParentPath_4_ok,
    tttLargeFiber50Block3Chunk0ParentPath_5_ok,
    tttLargeFiber50Block3Chunk0ParentPath_6_ok,
    tttLargeFiber50Block3Chunk0ParentPath_7_ok,
    tttLargeFiber50Block3Chunk0ParentPath_8_ok,
    tttLargeFiber50Block3Chunk0ParentPath_9_ok,
    tttLargeFiber50Block3Chunk0ParentPath_10_ok,
    tttLargeFiber50Block3Chunk0ParentPath_11_ok,
    tttLargeFiber50Block3Chunk0ParentPath_12_ok,
    tttLargeFiber50Block3Chunk0ParentPath_13_ok,
    tttLargeFiber50Block3Chunk0ParentPath_14_ok,
    tttLargeFiber50Block3Chunk0ParentPath_15_ok]

def tttLargeFiber50Block3Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block3Chunk0SourcesCheck &&
    tttLargeFiber50Block3Chunk0RowsAudit &&
    tttLargeFiber50Block3Chunk0ParentMapAudit &&
    tttLargeFiber50Block3Chunk0ParentsAudit

theorem tttLargeFiber50Block3Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber50Block3Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block3Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block3Chunk0SourcesCheck_ok,
    tttLargeFiber50Block3Chunk0RowsAudit_ok,
    tttLargeFiber50Block3Chunk0ParentMapAudit_ok,
    tttLargeFiber50Block3Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block3Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
