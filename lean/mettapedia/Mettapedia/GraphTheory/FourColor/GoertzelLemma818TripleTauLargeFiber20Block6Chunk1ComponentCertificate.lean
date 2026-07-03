import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 6 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block6Chunk1Sources : List Nat :=
  [   6416, 6417, 6418, 6419, 6420, 6421, 6422, 6423,
   6424, 6425, 6426, 6427, 6428, 6429, 6430, 6431]

def tttLargeFiber20Row400 : TripleComponentParentRow :=
  tripleRow 6416 6400 190 66 16 190 64 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row401 : TripleComponentParentRow :=
  tripleRow 6417 6401 190 66 17 190 64 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row402 : TripleComponentParentRow :=
  tripleRow 6418 6402 190 66 18 190 64 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row403 : TripleComponentParentRow :=
  tripleRow 6419 6403 190 66 19 190 64 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row404 : TripleComponentParentRow :=
  tripleRow 6420 6404 190 66 32 190 64 100
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row405 : TripleComponentParentRow :=
  tripleRow 6421 6405 190 66 33 190 64 101
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row406 : TripleComponentParentRow :=
  tripleRow 6422 6406 190 66 34 190 64 102
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row407 : TripleComponentParentRow :=
  tripleRow 6423 6407 190 66 35 190 64 103
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row408 : TripleComponentParentRow :=
  tripleRow 6424 6408 190 67 24 190 65 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row409 : TripleComponentParentRow :=
  tripleRow 6425 6409 190 67 25 190 65 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row410 : TripleComponentParentRow :=
  tripleRow 6426 6298 190 67 26 188 135 10
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber20Row411 : TripleComponentParentRow :=
  tripleRow 6427 6299 190 67 27 188 135 11
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber20Row412 : TripleComponentParentRow :=
  tripleRow 6428 6300 190 67 40 188 135 56
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber20Row413 : TripleComponentParentRow :=
  tripleRow 6429 6301 190 67 41 188 135 57
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber20Row414 : TripleComponentParentRow :=
  tripleRow 6430 6302 190 67 42 188 135 58
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber20Row415 : TripleComponentParentRow :=
  tripleRow 6431 6303 190 67 43 188 135 59
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber20Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row400
  , tttLargeFiber20Row401
  , tttLargeFiber20Row402
  , tttLargeFiber20Row403
  , tttLargeFiber20Row404
  , tttLargeFiber20Row405
  , tttLargeFiber20Row406
  , tttLargeFiber20Row407
  , tttLargeFiber20Row408
  , tttLargeFiber20Row409
  , tttLargeFiber20Row410
  , tttLargeFiber20Row411
  , tttLargeFiber20Row412
  , tttLargeFiber20Row413
  , tttLargeFiber20Row414
  , tttLargeFiber20Row415
  ]

def tttLargeFiber20Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber20Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber20Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber20Block6Chunk1Sources

theorem tttLargeFiber20Block6Chunk1SourcesCheck_ok :
    tttLargeFiber20Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber20Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block6Chunk1RowValid
    (listGetD tttLargeFiber20Block6Chunk1Rows i default)

def tttLargeFiber20Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block6Chunk1Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block6Chunk1Sources 0 0 == 6416
      && tttLargeFiber20ParentOf 6416 == 6400
      && tttLargeFiber20ParentOf 6400 == 6272
      && tttLargeFiber20ParentOf 6272 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block6Chunk1Sources 1 0 == 6417
      && tttLargeFiber20ParentOf 6417 == 6401
      && tttLargeFiber20ParentOf 6401 == 6273
      && tttLargeFiber20ParentOf 6273 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block6Chunk1Sources 2 0 == 6418
      && tttLargeFiber20ParentOf 6418 == 6402
      && tttLargeFiber20ParentOf 6402 == 6400
      && tttLargeFiber20ParentOf 6400 == 6272
      && tttLargeFiber20ParentOf 6272 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block6Chunk1Sources 3 0 == 6419
      && tttLargeFiber20ParentOf 6419 == 6403
      && tttLargeFiber20ParentOf 6403 == 6275
      && tttLargeFiber20ParentOf 6275 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block6Chunk1Sources 4 0 == 6420
      && tttLargeFiber20ParentOf 6420 == 6404
      && tttLargeFiber20ParentOf 6404 == 6276
      && tttLargeFiber20ParentOf 6276 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block6Chunk1Sources 5 0 == 6421
      && tttLargeFiber20ParentOf 6421 == 6405
      && tttLargeFiber20ParentOf 6405 == 6277
      && tttLargeFiber20ParentOf 6277 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block6Chunk1Sources 6 0 == 6422
      && tttLargeFiber20ParentOf 6422 == 6406
      && tttLargeFiber20ParentOf 6406 == 6401
      && tttLargeFiber20ParentOf 6401 == 6273
      && tttLargeFiber20ParentOf 6273 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block6Chunk1Sources 7 0 == 6423
      && tttLargeFiber20ParentOf 6423 == 6407
      && tttLargeFiber20ParentOf 6407 == 6400
      && tttLargeFiber20ParentOf 6400 == 6272
      && tttLargeFiber20ParentOf 6272 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block6Chunk1Sources 8 0 == 6424
      && tttLargeFiber20ParentOf 6424 == 6408
      && tttLargeFiber20ParentOf 6408 == 6280
      && tttLargeFiber20ParentOf 6280 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block6Chunk1Sources 9 0 == 6425
      && tttLargeFiber20ParentOf 6425 == 6409
      && tttLargeFiber20ParentOf 6409 == 6281
      && tttLargeFiber20ParentOf 6281 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block6Chunk1Sources 10 0 == 6426
      && tttLargeFiber20ParentOf 6426 == 6298
      && tttLargeFiber20ParentOf 6298 == 4666
      && tttLargeFiber20ParentOf 4666 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block6Chunk1Sources 11 0 == 6427
      && tttLargeFiber20ParentOf 6427 == 6299
      && tttLargeFiber20ParentOf 6299 == 4667
      && tttLargeFiber20ParentOf 4667 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block6Chunk1Sources 12 0 == 6428
      && tttLargeFiber20ParentOf 6428 == 6300
      && tttLargeFiber20ParentOf 6300 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block6Chunk1Sources 13 0 == 6429
      && tttLargeFiber20ParentOf 6429 == 6301
      && tttLargeFiber20ParentOf 6301 == 4669
      && tttLargeFiber20ParentOf 4669 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block6Chunk1Sources 14 0 == 6430
      && tttLargeFiber20ParentOf 6430 == 6302
      && tttLargeFiber20ParentOf 6302 == 4670
      && tttLargeFiber20ParentOf 4670 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block6Chunk1Sources 15 0 == 6431
      && tttLargeFiber20ParentOf 6431 == 6303
      && tttLargeFiber20ParentOf 6303 == 4671
      && tttLargeFiber20ParentOf 4671 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block6Chunk1Row_0_ok :
    tttLargeFiber20Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_1_ok :
    tttLargeFiber20Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_2_ok :
    tttLargeFiber20Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_3_ok :
    tttLargeFiber20Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_4_ok :
    tttLargeFiber20Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_5_ok :
    tttLargeFiber20Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_6_ok :
    tttLargeFiber20Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_7_ok :
    tttLargeFiber20Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_8_ok :
    tttLargeFiber20Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_9_ok :
    tttLargeFiber20Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_10_ok :
    tttLargeFiber20Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_11_ok :
    tttLargeFiber20Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_12_ok :
    tttLargeFiber20Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_13_ok :
    tttLargeFiber20Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_14_ok :
    tttLargeFiber20Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1Row_15_ok :
    tttLargeFiber20Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_0_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_1_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_2_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_3_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_4_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_5_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_6_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_7_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_8_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_9_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_10_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_11_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_12_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_13_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_14_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentMap_15_ok :
    tttLargeFiber20Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_0_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_1_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_2_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_3_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_4_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_5_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_6_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_7_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_8_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_9_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_10_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_11_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_12_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_13_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_14_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block6Chunk1ParentPath_15_ok :
    tttLargeFiber20Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber20Block6Chunk1RowCheck 0
    && tttLargeFiber20Block6Chunk1RowCheck 1
    && tttLargeFiber20Block6Chunk1RowCheck 2
    && tttLargeFiber20Block6Chunk1RowCheck 3
    && tttLargeFiber20Block6Chunk1RowCheck 4
    && tttLargeFiber20Block6Chunk1RowCheck 5
    && tttLargeFiber20Block6Chunk1RowCheck 6
    && tttLargeFiber20Block6Chunk1RowCheck 7
    && tttLargeFiber20Block6Chunk1RowCheck 8
    && tttLargeFiber20Block6Chunk1RowCheck 9
    && tttLargeFiber20Block6Chunk1RowCheck 10
    && tttLargeFiber20Block6Chunk1RowCheck 11
    && tttLargeFiber20Block6Chunk1RowCheck 12
    && tttLargeFiber20Block6Chunk1RowCheck 13
    && tttLargeFiber20Block6Chunk1RowCheck 14
    && tttLargeFiber20Block6Chunk1RowCheck 15

theorem tttLargeFiber20Block6Chunk1RowsAudit_ok :
    tttLargeFiber20Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber20Block6Chunk1RowsAudit,
    tttLargeFiber20Block6Chunk1Row_0_ok,
    tttLargeFiber20Block6Chunk1Row_1_ok,
    tttLargeFiber20Block6Chunk1Row_2_ok,
    tttLargeFiber20Block6Chunk1Row_3_ok,
    tttLargeFiber20Block6Chunk1Row_4_ok,
    tttLargeFiber20Block6Chunk1Row_5_ok,
    tttLargeFiber20Block6Chunk1Row_6_ok,
    tttLargeFiber20Block6Chunk1Row_7_ok,
    tttLargeFiber20Block6Chunk1Row_8_ok,
    tttLargeFiber20Block6Chunk1Row_9_ok,
    tttLargeFiber20Block6Chunk1Row_10_ok,
    tttLargeFiber20Block6Chunk1Row_11_ok,
    tttLargeFiber20Block6Chunk1Row_12_ok,
    tttLargeFiber20Block6Chunk1Row_13_ok,
    tttLargeFiber20Block6Chunk1Row_14_ok,
    tttLargeFiber20Block6Chunk1Row_15_ok]

def tttLargeFiber20Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber20Block6Chunk1ParentMapCheck 0
    && tttLargeFiber20Block6Chunk1ParentMapCheck 1
    && tttLargeFiber20Block6Chunk1ParentMapCheck 2
    && tttLargeFiber20Block6Chunk1ParentMapCheck 3
    && tttLargeFiber20Block6Chunk1ParentMapCheck 4
    && tttLargeFiber20Block6Chunk1ParentMapCheck 5
    && tttLargeFiber20Block6Chunk1ParentMapCheck 6
    && tttLargeFiber20Block6Chunk1ParentMapCheck 7
    && tttLargeFiber20Block6Chunk1ParentMapCheck 8
    && tttLargeFiber20Block6Chunk1ParentMapCheck 9
    && tttLargeFiber20Block6Chunk1ParentMapCheck 10
    && tttLargeFiber20Block6Chunk1ParentMapCheck 11
    && tttLargeFiber20Block6Chunk1ParentMapCheck 12
    && tttLargeFiber20Block6Chunk1ParentMapCheck 13
    && tttLargeFiber20Block6Chunk1ParentMapCheck 14
    && tttLargeFiber20Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber20Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber20Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber20Block6Chunk1ParentMapAudit,
    tttLargeFiber20Block6Chunk1ParentMap_0_ok,
    tttLargeFiber20Block6Chunk1ParentMap_1_ok,
    tttLargeFiber20Block6Chunk1ParentMap_2_ok,
    tttLargeFiber20Block6Chunk1ParentMap_3_ok,
    tttLargeFiber20Block6Chunk1ParentMap_4_ok,
    tttLargeFiber20Block6Chunk1ParentMap_5_ok,
    tttLargeFiber20Block6Chunk1ParentMap_6_ok,
    tttLargeFiber20Block6Chunk1ParentMap_7_ok,
    tttLargeFiber20Block6Chunk1ParentMap_8_ok,
    tttLargeFiber20Block6Chunk1ParentMap_9_ok,
    tttLargeFiber20Block6Chunk1ParentMap_10_ok,
    tttLargeFiber20Block6Chunk1ParentMap_11_ok,
    tttLargeFiber20Block6Chunk1ParentMap_12_ok,
    tttLargeFiber20Block6Chunk1ParentMap_13_ok,
    tttLargeFiber20Block6Chunk1ParentMap_14_ok,
    tttLargeFiber20Block6Chunk1ParentMap_15_ok]

def tttLargeFiber20Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber20Block6Chunk1ParentPathCheck 0
    && tttLargeFiber20Block6Chunk1ParentPathCheck 1
    && tttLargeFiber20Block6Chunk1ParentPathCheck 2
    && tttLargeFiber20Block6Chunk1ParentPathCheck 3
    && tttLargeFiber20Block6Chunk1ParentPathCheck 4
    && tttLargeFiber20Block6Chunk1ParentPathCheck 5
    && tttLargeFiber20Block6Chunk1ParentPathCheck 6
    && tttLargeFiber20Block6Chunk1ParentPathCheck 7
    && tttLargeFiber20Block6Chunk1ParentPathCheck 8
    && tttLargeFiber20Block6Chunk1ParentPathCheck 9
    && tttLargeFiber20Block6Chunk1ParentPathCheck 10
    && tttLargeFiber20Block6Chunk1ParentPathCheck 11
    && tttLargeFiber20Block6Chunk1ParentPathCheck 12
    && tttLargeFiber20Block6Chunk1ParentPathCheck 13
    && tttLargeFiber20Block6Chunk1ParentPathCheck 14
    && tttLargeFiber20Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber20Block6Chunk1ParentsAudit_ok :
    tttLargeFiber20Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber20Block6Chunk1ParentsAudit,
    tttLargeFiber20Block6Chunk1ParentPath_0_ok,
    tttLargeFiber20Block6Chunk1ParentPath_1_ok,
    tttLargeFiber20Block6Chunk1ParentPath_2_ok,
    tttLargeFiber20Block6Chunk1ParentPath_3_ok,
    tttLargeFiber20Block6Chunk1ParentPath_4_ok,
    tttLargeFiber20Block6Chunk1ParentPath_5_ok,
    tttLargeFiber20Block6Chunk1ParentPath_6_ok,
    tttLargeFiber20Block6Chunk1ParentPath_7_ok,
    tttLargeFiber20Block6Chunk1ParentPath_8_ok,
    tttLargeFiber20Block6Chunk1ParentPath_9_ok,
    tttLargeFiber20Block6Chunk1ParentPath_10_ok,
    tttLargeFiber20Block6Chunk1ParentPath_11_ok,
    tttLargeFiber20Block6Chunk1ParentPath_12_ok,
    tttLargeFiber20Block6Chunk1ParentPath_13_ok,
    tttLargeFiber20Block6Chunk1ParentPath_14_ok,
    tttLargeFiber20Block6Chunk1ParentPath_15_ok]

def tttLargeFiber20Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block6Chunk1SourcesCheck &&
    tttLargeFiber20Block6Chunk1RowsAudit &&
    tttLargeFiber20Block6Chunk1ParentMapAudit &&
    tttLargeFiber20Block6Chunk1ParentsAudit

theorem tttLargeFiber20Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber20Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block6Chunk1SourcesCheck_ok,
    tttLargeFiber20Block6Chunk1RowsAudit_ok,
    tttLargeFiber20Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber20Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
