import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 6 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block6Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block6Chunk0Sources : List Nat :=
  [   6400, 6401, 6402, 6403, 6404, 6405, 6406, 6407,
   6408, 6409, 6410, 6411, 6412, 6413, 6414, 6415]

def tttLargeFiber20Row384 : TripleComponentParentRow :=
  tripleRow 6400 6272 190 64 80 188 132 148
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row385 : TripleComponentParentRow :=
  tripleRow 6401 6273 190 64 81 188 132 149
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row386 : TripleComponentParentRow :=
  tripleRow 6402 6400 190 64 82 190 64 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row387 : TripleComponentParentRow :=
  tripleRow 6403 6275 190 64 83 188 132 151
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row388 : TripleComponentParentRow :=
  tripleRow 6404 6276 190 64 100 188 132 164
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row389 : TripleComponentParentRow :=
  tripleRow 6405 6277 190 64 101 188 132 165
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row390 : TripleComponentParentRow :=
  tripleRow 6406 6401 190 64 102 190 64 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row391 : TripleComponentParentRow :=
  tripleRow 6407 6400 190 64 103 190 64 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row392 : TripleComponentParentRow :=
  tripleRow 6408 6280 190 65 88 188 133 156
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row393 : TripleComponentParentRow :=
  tripleRow 6409 6281 190 65 89 188 133 157
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row394 : TripleComponentParentRow :=
  tripleRow 6410 6408 190 65 90 190 65 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row395 : TripleComponentParentRow :=
  tripleRow 6411 6283 190 65 91 188 133 159
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row396 : TripleComponentParentRow :=
  tripleRow 6412 6284 190 65 108 188 133 172
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row397 : TripleComponentParentRow :=
  tripleRow 6413 6285 190 65 109 188 133 173
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row398 : TripleComponentParentRow :=
  tripleRow 6414 6409 190 65 110 190 65 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row399 : TripleComponentParentRow :=
  tripleRow 6415 6408 190 65 111 190 65 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Block6Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row384
  , tttLargeFiber20Row385
  , tttLargeFiber20Row386
  , tttLargeFiber20Row387
  , tttLargeFiber20Row388
  , tttLargeFiber20Row389
  , tttLargeFiber20Row390
  , tttLargeFiber20Row391
  , tttLargeFiber20Row392
  , tttLargeFiber20Row393
  , tttLargeFiber20Row394
  , tttLargeFiber20Row395
  , tttLargeFiber20Row396
  , tttLargeFiber20Row397
  , tttLargeFiber20Row398
  , tttLargeFiber20Row399
  ]

def tttLargeFiber20Block6Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block6Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block6Chunk0ExpectedContains row.source &&
    tttLargeFiber20Block6Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block6Chunk0SourcesCheck : Bool :=
  (tttLargeFiber20Block6Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber20Block6Chunk0Sources

theorem tttLargeFiber20Block6Chunk0SourcesCheck_ok :
    tttLargeFiber20Block6Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber20Block6Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block6Chunk0RowValid
    (listGetD tttLargeFiber20Block6Chunk0Rows i default)

def tttLargeFiber20Block6Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block6Chunk0Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block6Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block6Chunk0Sources 0 0 == 6400
      && tttLargeFiber20ParentOf 6400 == 6272
      && tttLargeFiber20ParentOf 6272 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block6Chunk0Sources 1 0 == 6401
      && tttLargeFiber20ParentOf 6401 == 6273
      && tttLargeFiber20ParentOf 6273 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block6Chunk0Sources 2 0 == 6402
      && tttLargeFiber20ParentOf 6402 == 6400
      && tttLargeFiber20ParentOf 6400 == 6272
      && tttLargeFiber20ParentOf 6272 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block6Chunk0Sources 3 0 == 6403
      && tttLargeFiber20ParentOf 6403 == 6275
      && tttLargeFiber20ParentOf 6275 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block6Chunk0Sources 4 0 == 6404
      && tttLargeFiber20ParentOf 6404 == 6276
      && tttLargeFiber20ParentOf 6276 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block6Chunk0Sources 5 0 == 6405
      && tttLargeFiber20ParentOf 6405 == 6277
      && tttLargeFiber20ParentOf 6277 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block6Chunk0Sources 6 0 == 6406
      && tttLargeFiber20ParentOf 6406 == 6401
      && tttLargeFiber20ParentOf 6401 == 6273
      && tttLargeFiber20ParentOf 6273 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block6Chunk0Sources 7 0 == 6407
      && tttLargeFiber20ParentOf 6407 == 6400
      && tttLargeFiber20ParentOf 6400 == 6272
      && tttLargeFiber20ParentOf 6272 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block6Chunk0Sources 8 0 == 6408
      && tttLargeFiber20ParentOf 6408 == 6280
      && tttLargeFiber20ParentOf 6280 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block6Chunk0Sources 9 0 == 6409
      && tttLargeFiber20ParentOf 6409 == 6281
      && tttLargeFiber20ParentOf 6281 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block6Chunk0Sources 10 0 == 6410
      && tttLargeFiber20ParentOf 6410 == 6408
      && tttLargeFiber20ParentOf 6408 == 6280
      && tttLargeFiber20ParentOf 6280 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block6Chunk0Sources 11 0 == 6411
      && tttLargeFiber20ParentOf 6411 == 6283
      && tttLargeFiber20ParentOf 6283 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block6Chunk0Sources 12 0 == 6412
      && tttLargeFiber20ParentOf 6412 == 6284
      && tttLargeFiber20ParentOf 6284 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block6Chunk0Sources 13 0 == 6413
      && tttLargeFiber20ParentOf 6413 == 6285
      && tttLargeFiber20ParentOf 6285 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block6Chunk0Sources 14 0 == 6414
      && tttLargeFiber20ParentOf 6414 == 6409
      && tttLargeFiber20ParentOf 6409 == 6281
      && tttLargeFiber20ParentOf 6281 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block6Chunk0Sources 15 0 == 6415
      && tttLargeFiber20ParentOf 6415 == 6408
      && tttLargeFiber20ParentOf 6408 == 6280
      && tttLargeFiber20ParentOf 6280 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block6Chunk0Row_0_ok :
    tttLargeFiber20Block6Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_1_ok :
    tttLargeFiber20Block6Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_2_ok :
    tttLargeFiber20Block6Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_3_ok :
    tttLargeFiber20Block6Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_4_ok :
    tttLargeFiber20Block6Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_5_ok :
    tttLargeFiber20Block6Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_6_ok :
    tttLargeFiber20Block6Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_7_ok :
    tttLargeFiber20Block6Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_8_ok :
    tttLargeFiber20Block6Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_9_ok :
    tttLargeFiber20Block6Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_10_ok :
    tttLargeFiber20Block6Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_11_ok :
    tttLargeFiber20Block6Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_12_ok :
    tttLargeFiber20Block6Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_13_ok :
    tttLargeFiber20Block6Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_14_ok :
    tttLargeFiber20Block6Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0Row_15_ok :
    tttLargeFiber20Block6Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_0_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_1_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_2_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_3_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_4_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_5_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_6_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_7_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_8_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_9_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_10_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_11_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_12_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_13_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_14_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentMap_15_ok :
    tttLargeFiber20Block6Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_0_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_1_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_2_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_3_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_4_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_5_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_6_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_7_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_8_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_9_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_10_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_11_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_12_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_13_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_14_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block6Chunk0ParentPath_15_ok :
    tttLargeFiber20Block6Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block6Chunk0RowsAudit : Bool :=
  tttLargeFiber20Block6Chunk0RowCheck 0
    && tttLargeFiber20Block6Chunk0RowCheck 1
    && tttLargeFiber20Block6Chunk0RowCheck 2
    && tttLargeFiber20Block6Chunk0RowCheck 3
    && tttLargeFiber20Block6Chunk0RowCheck 4
    && tttLargeFiber20Block6Chunk0RowCheck 5
    && tttLargeFiber20Block6Chunk0RowCheck 6
    && tttLargeFiber20Block6Chunk0RowCheck 7
    && tttLargeFiber20Block6Chunk0RowCheck 8
    && tttLargeFiber20Block6Chunk0RowCheck 9
    && tttLargeFiber20Block6Chunk0RowCheck 10
    && tttLargeFiber20Block6Chunk0RowCheck 11
    && tttLargeFiber20Block6Chunk0RowCheck 12
    && tttLargeFiber20Block6Chunk0RowCheck 13
    && tttLargeFiber20Block6Chunk0RowCheck 14
    && tttLargeFiber20Block6Chunk0RowCheck 15

theorem tttLargeFiber20Block6Chunk0RowsAudit_ok :
    tttLargeFiber20Block6Chunk0RowsAudit = true := by
  simp [tttLargeFiber20Block6Chunk0RowsAudit,
    tttLargeFiber20Block6Chunk0Row_0_ok,
    tttLargeFiber20Block6Chunk0Row_1_ok,
    tttLargeFiber20Block6Chunk0Row_2_ok,
    tttLargeFiber20Block6Chunk0Row_3_ok,
    tttLargeFiber20Block6Chunk0Row_4_ok,
    tttLargeFiber20Block6Chunk0Row_5_ok,
    tttLargeFiber20Block6Chunk0Row_6_ok,
    tttLargeFiber20Block6Chunk0Row_7_ok,
    tttLargeFiber20Block6Chunk0Row_8_ok,
    tttLargeFiber20Block6Chunk0Row_9_ok,
    tttLargeFiber20Block6Chunk0Row_10_ok,
    tttLargeFiber20Block6Chunk0Row_11_ok,
    tttLargeFiber20Block6Chunk0Row_12_ok,
    tttLargeFiber20Block6Chunk0Row_13_ok,
    tttLargeFiber20Block6Chunk0Row_14_ok,
    tttLargeFiber20Block6Chunk0Row_15_ok]

def tttLargeFiber20Block6Chunk0ParentMapAudit : Bool :=
  tttLargeFiber20Block6Chunk0ParentMapCheck 0
    && tttLargeFiber20Block6Chunk0ParentMapCheck 1
    && tttLargeFiber20Block6Chunk0ParentMapCheck 2
    && tttLargeFiber20Block6Chunk0ParentMapCheck 3
    && tttLargeFiber20Block6Chunk0ParentMapCheck 4
    && tttLargeFiber20Block6Chunk0ParentMapCheck 5
    && tttLargeFiber20Block6Chunk0ParentMapCheck 6
    && tttLargeFiber20Block6Chunk0ParentMapCheck 7
    && tttLargeFiber20Block6Chunk0ParentMapCheck 8
    && tttLargeFiber20Block6Chunk0ParentMapCheck 9
    && tttLargeFiber20Block6Chunk0ParentMapCheck 10
    && tttLargeFiber20Block6Chunk0ParentMapCheck 11
    && tttLargeFiber20Block6Chunk0ParentMapCheck 12
    && tttLargeFiber20Block6Chunk0ParentMapCheck 13
    && tttLargeFiber20Block6Chunk0ParentMapCheck 14
    && tttLargeFiber20Block6Chunk0ParentMapCheck 15

theorem tttLargeFiber20Block6Chunk0ParentMapAudit_ok :
    tttLargeFiber20Block6Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber20Block6Chunk0ParentMapAudit,
    tttLargeFiber20Block6Chunk0ParentMap_0_ok,
    tttLargeFiber20Block6Chunk0ParentMap_1_ok,
    tttLargeFiber20Block6Chunk0ParentMap_2_ok,
    tttLargeFiber20Block6Chunk0ParentMap_3_ok,
    tttLargeFiber20Block6Chunk0ParentMap_4_ok,
    tttLargeFiber20Block6Chunk0ParentMap_5_ok,
    tttLargeFiber20Block6Chunk0ParentMap_6_ok,
    tttLargeFiber20Block6Chunk0ParentMap_7_ok,
    tttLargeFiber20Block6Chunk0ParentMap_8_ok,
    tttLargeFiber20Block6Chunk0ParentMap_9_ok,
    tttLargeFiber20Block6Chunk0ParentMap_10_ok,
    tttLargeFiber20Block6Chunk0ParentMap_11_ok,
    tttLargeFiber20Block6Chunk0ParentMap_12_ok,
    tttLargeFiber20Block6Chunk0ParentMap_13_ok,
    tttLargeFiber20Block6Chunk0ParentMap_14_ok,
    tttLargeFiber20Block6Chunk0ParentMap_15_ok]

def tttLargeFiber20Block6Chunk0ParentsAudit : Bool :=
  tttLargeFiber20Block6Chunk0ParentPathCheck 0
    && tttLargeFiber20Block6Chunk0ParentPathCheck 1
    && tttLargeFiber20Block6Chunk0ParentPathCheck 2
    && tttLargeFiber20Block6Chunk0ParentPathCheck 3
    && tttLargeFiber20Block6Chunk0ParentPathCheck 4
    && tttLargeFiber20Block6Chunk0ParentPathCheck 5
    && tttLargeFiber20Block6Chunk0ParentPathCheck 6
    && tttLargeFiber20Block6Chunk0ParentPathCheck 7
    && tttLargeFiber20Block6Chunk0ParentPathCheck 8
    && tttLargeFiber20Block6Chunk0ParentPathCheck 9
    && tttLargeFiber20Block6Chunk0ParentPathCheck 10
    && tttLargeFiber20Block6Chunk0ParentPathCheck 11
    && tttLargeFiber20Block6Chunk0ParentPathCheck 12
    && tttLargeFiber20Block6Chunk0ParentPathCheck 13
    && tttLargeFiber20Block6Chunk0ParentPathCheck 14
    && tttLargeFiber20Block6Chunk0ParentPathCheck 15

theorem tttLargeFiber20Block6Chunk0ParentsAudit_ok :
    tttLargeFiber20Block6Chunk0ParentsAudit = true := by
  simp [tttLargeFiber20Block6Chunk0ParentsAudit,
    tttLargeFiber20Block6Chunk0ParentPath_0_ok,
    tttLargeFiber20Block6Chunk0ParentPath_1_ok,
    tttLargeFiber20Block6Chunk0ParentPath_2_ok,
    tttLargeFiber20Block6Chunk0ParentPath_3_ok,
    tttLargeFiber20Block6Chunk0ParentPath_4_ok,
    tttLargeFiber20Block6Chunk0ParentPath_5_ok,
    tttLargeFiber20Block6Chunk0ParentPath_6_ok,
    tttLargeFiber20Block6Chunk0ParentPath_7_ok,
    tttLargeFiber20Block6Chunk0ParentPath_8_ok,
    tttLargeFiber20Block6Chunk0ParentPath_9_ok,
    tttLargeFiber20Block6Chunk0ParentPath_10_ok,
    tttLargeFiber20Block6Chunk0ParentPath_11_ok,
    tttLargeFiber20Block6Chunk0ParentPath_12_ok,
    tttLargeFiber20Block6Chunk0ParentPath_13_ok,
    tttLargeFiber20Block6Chunk0ParentPath_14_ok,
    tttLargeFiber20Block6Chunk0ParentPath_15_ok]

def tttLargeFiber20Block6Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block6Chunk0SourcesCheck &&
    tttLargeFiber20Block6Chunk0RowsAudit &&
    tttLargeFiber20Block6Chunk0ParentMapAudit &&
    tttLargeFiber20Block6Chunk0ParentsAudit

theorem tttLargeFiber20Block6Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber20Block6Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block6Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block6Chunk0SourcesCheck_ok,
    tttLargeFiber20Block6Chunk0RowsAudit_ok,
    tttLargeFiber20Block6Chunk0ParentMapAudit_ok,
    tttLargeFiber20Block6Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block6Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
