import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 2 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block2Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block2Chunk0Sources : List Nat :=
  [   5312, 5313, 5314, 5315, 5316, 5317, 5318, 5319,
   5320, 5321, 5322, 5323, 5324, 5325, 5326, 5327]

def tttLargeFiber50Row128 : TripleComponentParentRow :=
  tripleRow 5312 5344 158 0 80 158 48 148
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

def tttLargeFiber50Row129 : TripleComponentParentRow :=
  tripleRow 5313 5345 158 0 81 158 48 149
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

def tttLargeFiber50Row130 : TripleComponentParentRow :=
  tripleRow 5314 5312 158 0 82 158 0 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row131 : TripleComponentParentRow :=
  tripleRow 5315 5347 158 0 83 158 48 151
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

def tttLargeFiber50Row132 : TripleComponentParentRow :=
  tripleRow 5316 5348 158 0 100 158 48 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row133 : TripleComponentParentRow :=
  tripleRow 5317 5349 158 0 101 158 48 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row134 : TripleComponentParentRow :=
  tripleRow 5318 5313 158 0 102 158 0 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row135 : TripleComponentParentRow :=
  tripleRow 5319 5312 158 0 103 158 0 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Row136 : TripleComponentParentRow :=
  tripleRow 5320 5352 158 1 88 158 49 156
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

def tttLargeFiber50Row137 : TripleComponentParentRow :=
  tripleRow 5321 5353 158 1 89 158 49 157
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

def tttLargeFiber50Row138 : TripleComponentParentRow :=
  tripleRow 5322 5320 158 1 90 158 1 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row139 : TripleComponentParentRow :=
  tripleRow 5323 5355 158 1 91 158 49 159
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

def tttLargeFiber50Row140 : TripleComponentParentRow :=
  tripleRow 5324 5356 158 1 108 158 49 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row141 : TripleComponentParentRow :=
  tripleRow 5325 5357 158 1 109 158 49 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber50Row142 : TripleComponentParentRow :=
  tripleRow 5326 5321 158 1 110 158 1 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row143 : TripleComponentParentRow :=
  tripleRow 5327 5320 158 1 111 158 1 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Block2Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row128
  , tttLargeFiber50Row129
  , tttLargeFiber50Row130
  , tttLargeFiber50Row131
  , tttLargeFiber50Row132
  , tttLargeFiber50Row133
  , tttLargeFiber50Row134
  , tttLargeFiber50Row135
  , tttLargeFiber50Row136
  , tttLargeFiber50Row137
  , tttLargeFiber50Row138
  , tttLargeFiber50Row139
  , tttLargeFiber50Row140
  , tttLargeFiber50Row141
  , tttLargeFiber50Row142
  , tttLargeFiber50Row143
  ]

def tttLargeFiber50Block2Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block2Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block2Chunk0ExpectedContains row.source &&
    tttLargeFiber50Block2Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block2Chunk0SourcesCheck : Bool :=
  (tttLargeFiber50Block2Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber50Block2Chunk0Sources

theorem tttLargeFiber50Block2Chunk0SourcesCheck_ok :
    tttLargeFiber50Block2Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber50Block2Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block2Chunk0RowValid
    (listGetD tttLargeFiber50Block2Chunk0Rows i default)

def tttLargeFiber50Block2Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block2Chunk0Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block2Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block2Chunk0Sources 0 0 == 5312
      && tttLargeFiber50ParentOf 5312 == 5344
      && tttLargeFiber50ParentOf 5344 == 5248
      && tttLargeFiber50ParentOf 5248 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block2Chunk0Sources 1 0 == 5313
      && tttLargeFiber50ParentOf 5313 == 5345
      && tttLargeFiber50ParentOf 5345 == 5249
      && tttLargeFiber50ParentOf 5249 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block2Chunk0Sources 2 0 == 5314
      && tttLargeFiber50ParentOf 5314 == 5312
      && tttLargeFiber50ParentOf 5312 == 5344
      && tttLargeFiber50ParentOf 5344 == 5248
      && tttLargeFiber50ParentOf 5248 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block2Chunk0Sources 3 0 == 5315
      && tttLargeFiber50ParentOf 5315 == 5347
      && tttLargeFiber50ParentOf 5347 == 5251
      && tttLargeFiber50ParentOf 5251 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block2Chunk0Sources 4 0 == 5316
      && tttLargeFiber50ParentOf 5316 == 5348
      && tttLargeFiber50ParentOf 5348 == 5252
      && tttLargeFiber50ParentOf 5252 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block2Chunk0Sources 5 0 == 5317
      && tttLargeFiber50ParentOf 5317 == 5349
      && tttLargeFiber50ParentOf 5349 == 5253
      && tttLargeFiber50ParentOf 5253 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block2Chunk0Sources 6 0 == 5318
      && tttLargeFiber50ParentOf 5318 == 5313
      && tttLargeFiber50ParentOf 5313 == 5345
      && tttLargeFiber50ParentOf 5345 == 5249
      && tttLargeFiber50ParentOf 5249 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block2Chunk0Sources 7 0 == 5319
      && tttLargeFiber50ParentOf 5319 == 5312
      && tttLargeFiber50ParentOf 5312 == 5344
      && tttLargeFiber50ParentOf 5344 == 5248
      && tttLargeFiber50ParentOf 5248 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block2Chunk0Sources 8 0 == 5320
      && tttLargeFiber50ParentOf 5320 == 5352
      && tttLargeFiber50ParentOf 5352 == 5256
      && tttLargeFiber50ParentOf 5256 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block2Chunk0Sources 9 0 == 5321
      && tttLargeFiber50ParentOf 5321 == 5353
      && tttLargeFiber50ParentOf 5353 == 5257
      && tttLargeFiber50ParentOf 5257 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block2Chunk0Sources 10 0 == 5322
      && tttLargeFiber50ParentOf 5322 == 5320
      && tttLargeFiber50ParentOf 5320 == 5352
      && tttLargeFiber50ParentOf 5352 == 5256
      && tttLargeFiber50ParentOf 5256 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block2Chunk0Sources 11 0 == 5323
      && tttLargeFiber50ParentOf 5323 == 5355
      && tttLargeFiber50ParentOf 5355 == 5259
      && tttLargeFiber50ParentOf 5259 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block2Chunk0Sources 12 0 == 5324
      && tttLargeFiber50ParentOf 5324 == 5356
      && tttLargeFiber50ParentOf 5356 == 5260
      && tttLargeFiber50ParentOf 5260 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block2Chunk0Sources 13 0 == 5325
      && tttLargeFiber50ParentOf 5325 == 5357
      && tttLargeFiber50ParentOf 5357 == 5261
      && tttLargeFiber50ParentOf 5261 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (6 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block2Chunk0Sources 14 0 == 5326
      && tttLargeFiber50ParentOf 5326 == 5321
      && tttLargeFiber50ParentOf 5321 == 5353
      && tttLargeFiber50ParentOf 5353 == 5257
      && tttLargeFiber50ParentOf 5257 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (6 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block2Chunk0Sources 15 0 == 5327
      && tttLargeFiber50ParentOf 5327 == 5320
      && tttLargeFiber50ParentOf 5320 == 5352
      && tttLargeFiber50ParentOf 5352 == 5256
      && tttLargeFiber50ParentOf 5256 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block2Chunk0Row_0_ok :
    tttLargeFiber50Block2Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_1_ok :
    tttLargeFiber50Block2Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_2_ok :
    tttLargeFiber50Block2Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_3_ok :
    tttLargeFiber50Block2Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_4_ok :
    tttLargeFiber50Block2Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_5_ok :
    tttLargeFiber50Block2Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_6_ok :
    tttLargeFiber50Block2Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_7_ok :
    tttLargeFiber50Block2Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_8_ok :
    tttLargeFiber50Block2Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_9_ok :
    tttLargeFiber50Block2Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_10_ok :
    tttLargeFiber50Block2Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_11_ok :
    tttLargeFiber50Block2Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_12_ok :
    tttLargeFiber50Block2Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_13_ok :
    tttLargeFiber50Block2Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_14_ok :
    tttLargeFiber50Block2Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0Row_15_ok :
    tttLargeFiber50Block2Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_0_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_1_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_2_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_3_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_4_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_5_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_6_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_7_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_8_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_9_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_10_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_11_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_12_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_13_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_14_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentMap_15_ok :
    tttLargeFiber50Block2Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_0_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_1_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_2_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_3_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_4_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_5_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_6_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_7_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_8_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_9_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_10_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_11_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_12_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_13_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_14_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block2Chunk0ParentPath_15_ok :
    tttLargeFiber50Block2Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block2Chunk0RowsAudit : Bool :=
  tttLargeFiber50Block2Chunk0RowCheck 0
    && tttLargeFiber50Block2Chunk0RowCheck 1
    && tttLargeFiber50Block2Chunk0RowCheck 2
    && tttLargeFiber50Block2Chunk0RowCheck 3
    && tttLargeFiber50Block2Chunk0RowCheck 4
    && tttLargeFiber50Block2Chunk0RowCheck 5
    && tttLargeFiber50Block2Chunk0RowCheck 6
    && tttLargeFiber50Block2Chunk0RowCheck 7
    && tttLargeFiber50Block2Chunk0RowCheck 8
    && tttLargeFiber50Block2Chunk0RowCheck 9
    && tttLargeFiber50Block2Chunk0RowCheck 10
    && tttLargeFiber50Block2Chunk0RowCheck 11
    && tttLargeFiber50Block2Chunk0RowCheck 12
    && tttLargeFiber50Block2Chunk0RowCheck 13
    && tttLargeFiber50Block2Chunk0RowCheck 14
    && tttLargeFiber50Block2Chunk0RowCheck 15

theorem tttLargeFiber50Block2Chunk0RowsAudit_ok :
    tttLargeFiber50Block2Chunk0RowsAudit = true := by
  simp [tttLargeFiber50Block2Chunk0RowsAudit,
    tttLargeFiber50Block2Chunk0Row_0_ok,
    tttLargeFiber50Block2Chunk0Row_1_ok,
    tttLargeFiber50Block2Chunk0Row_2_ok,
    tttLargeFiber50Block2Chunk0Row_3_ok,
    tttLargeFiber50Block2Chunk0Row_4_ok,
    tttLargeFiber50Block2Chunk0Row_5_ok,
    tttLargeFiber50Block2Chunk0Row_6_ok,
    tttLargeFiber50Block2Chunk0Row_7_ok,
    tttLargeFiber50Block2Chunk0Row_8_ok,
    tttLargeFiber50Block2Chunk0Row_9_ok,
    tttLargeFiber50Block2Chunk0Row_10_ok,
    tttLargeFiber50Block2Chunk0Row_11_ok,
    tttLargeFiber50Block2Chunk0Row_12_ok,
    tttLargeFiber50Block2Chunk0Row_13_ok,
    tttLargeFiber50Block2Chunk0Row_14_ok,
    tttLargeFiber50Block2Chunk0Row_15_ok]

def tttLargeFiber50Block2Chunk0ParentMapAudit : Bool :=
  tttLargeFiber50Block2Chunk0ParentMapCheck 0
    && tttLargeFiber50Block2Chunk0ParentMapCheck 1
    && tttLargeFiber50Block2Chunk0ParentMapCheck 2
    && tttLargeFiber50Block2Chunk0ParentMapCheck 3
    && tttLargeFiber50Block2Chunk0ParentMapCheck 4
    && tttLargeFiber50Block2Chunk0ParentMapCheck 5
    && tttLargeFiber50Block2Chunk0ParentMapCheck 6
    && tttLargeFiber50Block2Chunk0ParentMapCheck 7
    && tttLargeFiber50Block2Chunk0ParentMapCheck 8
    && tttLargeFiber50Block2Chunk0ParentMapCheck 9
    && tttLargeFiber50Block2Chunk0ParentMapCheck 10
    && tttLargeFiber50Block2Chunk0ParentMapCheck 11
    && tttLargeFiber50Block2Chunk0ParentMapCheck 12
    && tttLargeFiber50Block2Chunk0ParentMapCheck 13
    && tttLargeFiber50Block2Chunk0ParentMapCheck 14
    && tttLargeFiber50Block2Chunk0ParentMapCheck 15

theorem tttLargeFiber50Block2Chunk0ParentMapAudit_ok :
    tttLargeFiber50Block2Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber50Block2Chunk0ParentMapAudit,
    tttLargeFiber50Block2Chunk0ParentMap_0_ok,
    tttLargeFiber50Block2Chunk0ParentMap_1_ok,
    tttLargeFiber50Block2Chunk0ParentMap_2_ok,
    tttLargeFiber50Block2Chunk0ParentMap_3_ok,
    tttLargeFiber50Block2Chunk0ParentMap_4_ok,
    tttLargeFiber50Block2Chunk0ParentMap_5_ok,
    tttLargeFiber50Block2Chunk0ParentMap_6_ok,
    tttLargeFiber50Block2Chunk0ParentMap_7_ok,
    tttLargeFiber50Block2Chunk0ParentMap_8_ok,
    tttLargeFiber50Block2Chunk0ParentMap_9_ok,
    tttLargeFiber50Block2Chunk0ParentMap_10_ok,
    tttLargeFiber50Block2Chunk0ParentMap_11_ok,
    tttLargeFiber50Block2Chunk0ParentMap_12_ok,
    tttLargeFiber50Block2Chunk0ParentMap_13_ok,
    tttLargeFiber50Block2Chunk0ParentMap_14_ok,
    tttLargeFiber50Block2Chunk0ParentMap_15_ok]

def tttLargeFiber50Block2Chunk0ParentsAudit : Bool :=
  tttLargeFiber50Block2Chunk0ParentPathCheck 0
    && tttLargeFiber50Block2Chunk0ParentPathCheck 1
    && tttLargeFiber50Block2Chunk0ParentPathCheck 2
    && tttLargeFiber50Block2Chunk0ParentPathCheck 3
    && tttLargeFiber50Block2Chunk0ParentPathCheck 4
    && tttLargeFiber50Block2Chunk0ParentPathCheck 5
    && tttLargeFiber50Block2Chunk0ParentPathCheck 6
    && tttLargeFiber50Block2Chunk0ParentPathCheck 7
    && tttLargeFiber50Block2Chunk0ParentPathCheck 8
    && tttLargeFiber50Block2Chunk0ParentPathCheck 9
    && tttLargeFiber50Block2Chunk0ParentPathCheck 10
    && tttLargeFiber50Block2Chunk0ParentPathCheck 11
    && tttLargeFiber50Block2Chunk0ParentPathCheck 12
    && tttLargeFiber50Block2Chunk0ParentPathCheck 13
    && tttLargeFiber50Block2Chunk0ParentPathCheck 14
    && tttLargeFiber50Block2Chunk0ParentPathCheck 15

theorem tttLargeFiber50Block2Chunk0ParentsAudit_ok :
    tttLargeFiber50Block2Chunk0ParentsAudit = true := by
  simp [tttLargeFiber50Block2Chunk0ParentsAudit,
    tttLargeFiber50Block2Chunk0ParentPath_0_ok,
    tttLargeFiber50Block2Chunk0ParentPath_1_ok,
    tttLargeFiber50Block2Chunk0ParentPath_2_ok,
    tttLargeFiber50Block2Chunk0ParentPath_3_ok,
    tttLargeFiber50Block2Chunk0ParentPath_4_ok,
    tttLargeFiber50Block2Chunk0ParentPath_5_ok,
    tttLargeFiber50Block2Chunk0ParentPath_6_ok,
    tttLargeFiber50Block2Chunk0ParentPath_7_ok,
    tttLargeFiber50Block2Chunk0ParentPath_8_ok,
    tttLargeFiber50Block2Chunk0ParentPath_9_ok,
    tttLargeFiber50Block2Chunk0ParentPath_10_ok,
    tttLargeFiber50Block2Chunk0ParentPath_11_ok,
    tttLargeFiber50Block2Chunk0ParentPath_12_ok,
    tttLargeFiber50Block2Chunk0ParentPath_13_ok,
    tttLargeFiber50Block2Chunk0ParentPath_14_ok,
    tttLargeFiber50Block2Chunk0ParentPath_15_ok]

def tttLargeFiber50Block2Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block2Chunk0SourcesCheck &&
    tttLargeFiber50Block2Chunk0RowsAudit &&
    tttLargeFiber50Block2Chunk0ParentMapAudit &&
    tttLargeFiber50Block2Chunk0ParentsAudit

theorem tttLargeFiber50Block2Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber50Block2Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block2Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block2Chunk0SourcesCheck_ok,
    tttLargeFiber50Block2Chunk0RowsAudit_ok,
    tttLargeFiber50Block2Chunk0ParentMapAudit_ok,
    tttLargeFiber50Block2Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block2Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
