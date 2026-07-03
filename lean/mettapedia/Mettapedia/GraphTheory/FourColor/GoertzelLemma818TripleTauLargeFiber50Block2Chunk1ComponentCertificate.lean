import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 2 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block2Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block2Chunk1Sources : List Nat :=
  [   5328, 5329, 5330, 5331, 5332, 5333, 5334, 5335,
   5336, 5337, 5338, 5339, 5340, 5341, 5342, 5343]

def tttLargeFiber50Row144 : TripleComponentParentRow :=
  tripleRow 5328 5332 158 2 16 158 2 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row145 : TripleComponentParentRow :=
  tripleRow 5329 5333 158 2 17 158 2 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row146 : TripleComponentParentRow :=
  tripleRow 5330 5284 158 2 18 157 172 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber50Row147 : TripleComponentParentRow :=
  tripleRow 5331 5285 158 2 19 157 172 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber50Row148 : TripleComponentParentRow :=
  tripleRow 5332 5280 158 2 32 157 172 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row149 : TripleComponentParentRow :=
  tripleRow 5333 5281 158 2 33 157 172 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row150 : TripleComponentParentRow :=
  tripleRow 5334 5282 158 2 34 157 172 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row151 : TripleComponentParentRow :=
  tripleRow 5335 5283 158 2 35 157 172 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row152 : TripleComponentParentRow :=
  tripleRow 5336 5340 158 3 24 158 3 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row153 : TripleComponentParentRow :=
  tripleRow 5337 5341 158 3 25 158 3 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row154 : TripleComponentParentRow :=
  tripleRow 5338 5292 158 3 26 157 173 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber50Row155 : TripleComponentParentRow :=
  tripleRow 5339 5293 158 3 27 157 173 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber50Row156 : TripleComponentParentRow :=
  tripleRow 5340 5288 158 3 40 157 173 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row157 : TripleComponentParentRow :=
  tripleRow 5341 5289 158 3 41 157 173 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row158 : TripleComponentParentRow :=
  tripleRow 5342 5290 158 3 42 157 173 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Row159 : TripleComponentParentRow :=
  tripleRow 5343 5291 158 3 43 157 173 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber50Block2Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row144
  , tttLargeFiber50Row145
  , tttLargeFiber50Row146
  , tttLargeFiber50Row147
  , tttLargeFiber50Row148
  , tttLargeFiber50Row149
  , tttLargeFiber50Row150
  , tttLargeFiber50Row151
  , tttLargeFiber50Row152
  , tttLargeFiber50Row153
  , tttLargeFiber50Row154
  , tttLargeFiber50Row155
  , tttLargeFiber50Row156
  , tttLargeFiber50Row157
  , tttLargeFiber50Row158
  , tttLargeFiber50Row159
  ]

def tttLargeFiber50Block2Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block2Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block2Chunk1ExpectedContains row.source &&
    tttLargeFiber50Block2Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block2Chunk1SourcesCheck : Bool :=
  (tttLargeFiber50Block2Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber50Block2Chunk1Sources

theorem tttLargeFiber50Block2Chunk1SourcesCheck_ok :
    tttLargeFiber50Block2Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber50Block2Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block2Chunk1RowValid
    (listGetD tttLargeFiber50Block2Chunk1Rows i default)

def tttLargeFiber50Block2Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block2Chunk1Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block2Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block2Chunk1Sources 0 0 == 5328
      && tttLargeFiber50ParentOf 5328 == 5332
      && tttLargeFiber50ParentOf 5332 == 5280
      && tttLargeFiber50ParentOf 5280 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block2Chunk1Sources 1 0 == 5329
      && tttLargeFiber50ParentOf 5329 == 5333
      && tttLargeFiber50ParentOf 5333 == 5281
      && tttLargeFiber50ParentOf 5281 == 5217
      && tttLargeFiber50ParentOf 5217 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block2Chunk1Sources 2 0 == 5330
      && tttLargeFiber50ParentOf 5330 == 5284
      && tttLargeFiber50ParentOf 5284 == 5220
      && tttLargeFiber50ParentOf 5220 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block2Chunk1Sources 3 0 == 5331
      && tttLargeFiber50ParentOf 5331 == 5285
      && tttLargeFiber50ParentOf 5285 == 5221
      && tttLargeFiber50ParentOf 5221 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block2Chunk1Sources 4 0 == 5332
      && tttLargeFiber50ParentOf 5332 == 5280
      && tttLargeFiber50ParentOf 5280 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block2Chunk1Sources 5 0 == 5333
      && tttLargeFiber50ParentOf 5333 == 5281
      && tttLargeFiber50ParentOf 5281 == 5217
      && tttLargeFiber50ParentOf 5217 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block2Chunk1Sources 6 0 == 5334
      && tttLargeFiber50ParentOf 5334 == 5282
      && tttLargeFiber50ParentOf 5282 == 5218
      && tttLargeFiber50ParentOf 5218 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block2Chunk1Sources 7 0 == 5335
      && tttLargeFiber50ParentOf 5335 == 5283
      && tttLargeFiber50ParentOf 5283 == 5219
      && tttLargeFiber50ParentOf 5219 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block2Chunk1Sources 8 0 == 5336
      && tttLargeFiber50ParentOf 5336 == 5340
      && tttLargeFiber50ParentOf 5340 == 5288
      && tttLargeFiber50ParentOf 5288 == 5224
      && tttLargeFiber50ParentOf 5224 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block2Chunk1Sources 9 0 == 5337
      && tttLargeFiber50ParentOf 5337 == 5341
      && tttLargeFiber50ParentOf 5341 == 5289
      && tttLargeFiber50ParentOf 5289 == 5225
      && tttLargeFiber50ParentOf 5225 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (6 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block2Chunk1Sources 10 0 == 5338
      && tttLargeFiber50ParentOf 5338 == 5292
      && tttLargeFiber50ParentOf 5292 == 5228
      && tttLargeFiber50ParentOf 5228 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block2Chunk1Sources 11 0 == 5339
      && tttLargeFiber50ParentOf 5339 == 5293
      && tttLargeFiber50ParentOf 5293 == 5229
      && tttLargeFiber50ParentOf 5229 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (6 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block2Chunk1Sources 12 0 == 5340
      && tttLargeFiber50ParentOf 5340 == 5288
      && tttLargeFiber50ParentOf 5288 == 5224
      && tttLargeFiber50ParentOf 5224 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block2Chunk1Sources 13 0 == 5341
      && tttLargeFiber50ParentOf 5341 == 5289
      && tttLargeFiber50ParentOf 5289 == 5225
      && tttLargeFiber50ParentOf 5225 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block2Chunk1Sources 14 0 == 5342
      && tttLargeFiber50ParentOf 5342 == 5290
      && tttLargeFiber50ParentOf 5290 == 5226
      && tttLargeFiber50ParentOf 5226 == 5194
      && tttLargeFiber50ParentOf 5194 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (6 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block2Chunk1Sources 15 0 == 5343
      && tttLargeFiber50ParentOf 5343 == 5291
      && tttLargeFiber50ParentOf 5291 == 5227
      && tttLargeFiber50ParentOf 5227 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block2Chunk1Row_0_ok :
    tttLargeFiber50Block2Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_1_ok :
    tttLargeFiber50Block2Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_2_ok :
    tttLargeFiber50Block2Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_3_ok :
    tttLargeFiber50Block2Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_4_ok :
    tttLargeFiber50Block2Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_5_ok :
    tttLargeFiber50Block2Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_6_ok :
    tttLargeFiber50Block2Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_7_ok :
    tttLargeFiber50Block2Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_8_ok :
    tttLargeFiber50Block2Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_9_ok :
    tttLargeFiber50Block2Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_10_ok :
    tttLargeFiber50Block2Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_11_ok :
    tttLargeFiber50Block2Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_12_ok :
    tttLargeFiber50Block2Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_13_ok :
    tttLargeFiber50Block2Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_14_ok :
    tttLargeFiber50Block2Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1Row_15_ok :
    tttLargeFiber50Block2Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_0_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_1_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_2_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_3_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_4_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_5_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_6_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_7_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_8_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_9_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_10_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_11_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_12_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_13_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_14_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentMap_15_ok :
    tttLargeFiber50Block2Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_0_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_1_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_2_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_3_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_4_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_5_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_6_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_7_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_8_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_9_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_10_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_11_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_12_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_13_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_14_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block2Chunk1ParentPath_15_ok :
    tttLargeFiber50Block2Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block2Chunk1RowsAudit : Bool :=
  tttLargeFiber50Block2Chunk1RowCheck 0
    && tttLargeFiber50Block2Chunk1RowCheck 1
    && tttLargeFiber50Block2Chunk1RowCheck 2
    && tttLargeFiber50Block2Chunk1RowCheck 3
    && tttLargeFiber50Block2Chunk1RowCheck 4
    && tttLargeFiber50Block2Chunk1RowCheck 5
    && tttLargeFiber50Block2Chunk1RowCheck 6
    && tttLargeFiber50Block2Chunk1RowCheck 7
    && tttLargeFiber50Block2Chunk1RowCheck 8
    && tttLargeFiber50Block2Chunk1RowCheck 9
    && tttLargeFiber50Block2Chunk1RowCheck 10
    && tttLargeFiber50Block2Chunk1RowCheck 11
    && tttLargeFiber50Block2Chunk1RowCheck 12
    && tttLargeFiber50Block2Chunk1RowCheck 13
    && tttLargeFiber50Block2Chunk1RowCheck 14
    && tttLargeFiber50Block2Chunk1RowCheck 15

theorem tttLargeFiber50Block2Chunk1RowsAudit_ok :
    tttLargeFiber50Block2Chunk1RowsAudit = true := by
  simp [tttLargeFiber50Block2Chunk1RowsAudit,
    tttLargeFiber50Block2Chunk1Row_0_ok,
    tttLargeFiber50Block2Chunk1Row_1_ok,
    tttLargeFiber50Block2Chunk1Row_2_ok,
    tttLargeFiber50Block2Chunk1Row_3_ok,
    tttLargeFiber50Block2Chunk1Row_4_ok,
    tttLargeFiber50Block2Chunk1Row_5_ok,
    tttLargeFiber50Block2Chunk1Row_6_ok,
    tttLargeFiber50Block2Chunk1Row_7_ok,
    tttLargeFiber50Block2Chunk1Row_8_ok,
    tttLargeFiber50Block2Chunk1Row_9_ok,
    tttLargeFiber50Block2Chunk1Row_10_ok,
    tttLargeFiber50Block2Chunk1Row_11_ok,
    tttLargeFiber50Block2Chunk1Row_12_ok,
    tttLargeFiber50Block2Chunk1Row_13_ok,
    tttLargeFiber50Block2Chunk1Row_14_ok,
    tttLargeFiber50Block2Chunk1Row_15_ok]

def tttLargeFiber50Block2Chunk1ParentMapAudit : Bool :=
  tttLargeFiber50Block2Chunk1ParentMapCheck 0
    && tttLargeFiber50Block2Chunk1ParentMapCheck 1
    && tttLargeFiber50Block2Chunk1ParentMapCheck 2
    && tttLargeFiber50Block2Chunk1ParentMapCheck 3
    && tttLargeFiber50Block2Chunk1ParentMapCheck 4
    && tttLargeFiber50Block2Chunk1ParentMapCheck 5
    && tttLargeFiber50Block2Chunk1ParentMapCheck 6
    && tttLargeFiber50Block2Chunk1ParentMapCheck 7
    && tttLargeFiber50Block2Chunk1ParentMapCheck 8
    && tttLargeFiber50Block2Chunk1ParentMapCheck 9
    && tttLargeFiber50Block2Chunk1ParentMapCheck 10
    && tttLargeFiber50Block2Chunk1ParentMapCheck 11
    && tttLargeFiber50Block2Chunk1ParentMapCheck 12
    && tttLargeFiber50Block2Chunk1ParentMapCheck 13
    && tttLargeFiber50Block2Chunk1ParentMapCheck 14
    && tttLargeFiber50Block2Chunk1ParentMapCheck 15

theorem tttLargeFiber50Block2Chunk1ParentMapAudit_ok :
    tttLargeFiber50Block2Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber50Block2Chunk1ParentMapAudit,
    tttLargeFiber50Block2Chunk1ParentMap_0_ok,
    tttLargeFiber50Block2Chunk1ParentMap_1_ok,
    tttLargeFiber50Block2Chunk1ParentMap_2_ok,
    tttLargeFiber50Block2Chunk1ParentMap_3_ok,
    tttLargeFiber50Block2Chunk1ParentMap_4_ok,
    tttLargeFiber50Block2Chunk1ParentMap_5_ok,
    tttLargeFiber50Block2Chunk1ParentMap_6_ok,
    tttLargeFiber50Block2Chunk1ParentMap_7_ok,
    tttLargeFiber50Block2Chunk1ParentMap_8_ok,
    tttLargeFiber50Block2Chunk1ParentMap_9_ok,
    tttLargeFiber50Block2Chunk1ParentMap_10_ok,
    tttLargeFiber50Block2Chunk1ParentMap_11_ok,
    tttLargeFiber50Block2Chunk1ParentMap_12_ok,
    tttLargeFiber50Block2Chunk1ParentMap_13_ok,
    tttLargeFiber50Block2Chunk1ParentMap_14_ok,
    tttLargeFiber50Block2Chunk1ParentMap_15_ok]

def tttLargeFiber50Block2Chunk1ParentsAudit : Bool :=
  tttLargeFiber50Block2Chunk1ParentPathCheck 0
    && tttLargeFiber50Block2Chunk1ParentPathCheck 1
    && tttLargeFiber50Block2Chunk1ParentPathCheck 2
    && tttLargeFiber50Block2Chunk1ParentPathCheck 3
    && tttLargeFiber50Block2Chunk1ParentPathCheck 4
    && tttLargeFiber50Block2Chunk1ParentPathCheck 5
    && tttLargeFiber50Block2Chunk1ParentPathCheck 6
    && tttLargeFiber50Block2Chunk1ParentPathCheck 7
    && tttLargeFiber50Block2Chunk1ParentPathCheck 8
    && tttLargeFiber50Block2Chunk1ParentPathCheck 9
    && tttLargeFiber50Block2Chunk1ParentPathCheck 10
    && tttLargeFiber50Block2Chunk1ParentPathCheck 11
    && tttLargeFiber50Block2Chunk1ParentPathCheck 12
    && tttLargeFiber50Block2Chunk1ParentPathCheck 13
    && tttLargeFiber50Block2Chunk1ParentPathCheck 14
    && tttLargeFiber50Block2Chunk1ParentPathCheck 15

theorem tttLargeFiber50Block2Chunk1ParentsAudit_ok :
    tttLargeFiber50Block2Chunk1ParentsAudit = true := by
  simp [tttLargeFiber50Block2Chunk1ParentsAudit,
    tttLargeFiber50Block2Chunk1ParentPath_0_ok,
    tttLargeFiber50Block2Chunk1ParentPath_1_ok,
    tttLargeFiber50Block2Chunk1ParentPath_2_ok,
    tttLargeFiber50Block2Chunk1ParentPath_3_ok,
    tttLargeFiber50Block2Chunk1ParentPath_4_ok,
    tttLargeFiber50Block2Chunk1ParentPath_5_ok,
    tttLargeFiber50Block2Chunk1ParentPath_6_ok,
    tttLargeFiber50Block2Chunk1ParentPath_7_ok,
    tttLargeFiber50Block2Chunk1ParentPath_8_ok,
    tttLargeFiber50Block2Chunk1ParentPath_9_ok,
    tttLargeFiber50Block2Chunk1ParentPath_10_ok,
    tttLargeFiber50Block2Chunk1ParentPath_11_ok,
    tttLargeFiber50Block2Chunk1ParentPath_12_ok,
    tttLargeFiber50Block2Chunk1ParentPath_13_ok,
    tttLargeFiber50Block2Chunk1ParentPath_14_ok,
    tttLargeFiber50Block2Chunk1ParentPath_15_ok]

def tttLargeFiber50Block2Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block2Chunk1SourcesCheck &&
    tttLargeFiber50Block2Chunk1RowsAudit &&
    tttLargeFiber50Block2Chunk1ParentMapAudit &&
    tttLargeFiber50Block2Chunk1ParentsAudit

theorem tttLargeFiber50Block2Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber50Block2Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block2Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block2Chunk1SourcesCheck_ok,
    tttLargeFiber50Block2Chunk1RowsAudit_ok,
    tttLargeFiber50Block2Chunk1ParentMapAudit_ok,
    tttLargeFiber50Block2Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block2Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
