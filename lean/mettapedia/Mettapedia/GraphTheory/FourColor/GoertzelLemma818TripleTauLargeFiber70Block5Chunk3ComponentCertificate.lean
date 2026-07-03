import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 5 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block5Chunk3Sources : List Nat :=
  [   3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399,
   3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407]

def tttLargeFiber70Row368 : TripleComponentParentRow :=
  tripleRow 3392 3520 101 190 64 103 126 64
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row369 : TripleComponentParentRow :=
  tripleRow 3393 3521 101 190 65 103 126 65
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row370 : TripleComponentParentRow :=
  tripleRow 3394 3522 101 190 66 103 126 66
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row371 : TripleComponentParentRow :=
  tripleRow 3395 3379 101 190 67 101 188 135
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row372 : TripleComponentParentRow :=
  tripleRow 3396 3364 101 190 116 101 142 48
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber70Row373 : TripleComponentParentRow :=
  tripleRow 3397 3365 101 190 117 101 142 49
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row374 : TripleComponentParentRow :=
  tripleRow 3398 3526 101 190 118 103 126 118
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row375 : TripleComponentParentRow :=
  tripleRow 3399 3527 101 190 119 103 126 119
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row376 : TripleComponentParentRow :=
  tripleRow 3400 3528 101 191 72 103 127 72
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row377 : TripleComponentParentRow :=
  tripleRow 3401 3529 101 191 73 103 127 73
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row378 : TripleComponentParentRow :=
  tripleRow 3402 3530 101 191 74 103 127 74
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row379 : TripleComponentParentRow :=
  tripleRow 3403 3531 101 191 75 103 127 75
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row380 : TripleComponentParentRow :=
  tripleRow 3404 3372 101 191 124 101 143 56
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber70Row381 : TripleComponentParentRow :=
  tripleRow 3405 3373 101 191 125 101 143 57
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row382 : TripleComponentParentRow :=
  tripleRow 3406 3534 101 191 126 103 127 126
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Row383 : TripleComponentParentRow :=
  tripleRow 3407 3535 101 191 127 103 127 127
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber70Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row368
  , tttLargeFiber70Row369
  , tttLargeFiber70Row370
  , tttLargeFiber70Row371
  , tttLargeFiber70Row372
  , tttLargeFiber70Row373
  , tttLargeFiber70Row374
  , tttLargeFiber70Row375
  , tttLargeFiber70Row376
  , tttLargeFiber70Row377
  , tttLargeFiber70Row378
  , tttLargeFiber70Row379
  , tttLargeFiber70Row380
  , tttLargeFiber70Row381
  , tttLargeFiber70Row382
  , tttLargeFiber70Row383
  ]

def tttLargeFiber70Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber70Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber70Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber70Block5Chunk3Sources

theorem tttLargeFiber70Block5Chunk3SourcesCheck_ok :
    tttLargeFiber70Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber70Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block5Chunk3RowValid
    (listGetD tttLargeFiber70Block5Chunk3Rows i default)

def tttLargeFiber70Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block5Chunk3Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block5Chunk3Sources 0 0 == 3392
      && tttLargeFiber70ParentOf 3392 == 3520
      && tttLargeFiber70ParentOf 3520 == 2768
      && tttLargeFiber70ParentOf 2768 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block5Chunk3Sources 1 0 == 3393
      && tttLargeFiber70ParentOf 3393 == 3521
      && tttLargeFiber70ParentOf 3521 == 2769
      && tttLargeFiber70ParentOf 2769 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block5Chunk3Sources 2 0 == 3394
      && tttLargeFiber70ParentOf 3394 == 3522
      && tttLargeFiber70ParentOf 3522 == 2770
      && tttLargeFiber70ParentOf 2770 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block5Chunk3Sources 3 0 == 3395
      && tttLargeFiber70ParentOf 3395 == 3379
      && tttLargeFiber70ParentOf 3379 == 3347
      && tttLargeFiber70ParentOf 3347 == 3344
      && tttLargeFiber70ParentOf 3344 == 3472
      && tttLargeFiber70ParentOf 3472 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block5Chunk3Sources 4 0 == 3396
      && tttLargeFiber70ParentOf 3396 == 3364
      && tttLargeFiber70ParentOf 3364 == 3352
      && tttLargeFiber70ParentOf 3352 == 3480
      && tttLargeFiber70ParentOf 3480 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block5Chunk3Sources 5 0 == 3397
      && tttLargeFiber70ParentOf 3397 == 3365
      && tttLargeFiber70ParentOf 3365 == 3353
      && tttLargeFiber70ParentOf 3353 == 3481
      && tttLargeFiber70ParentOf 3481 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block5Chunk3Sources 6 0 == 3398
      && tttLargeFiber70ParentOf 3398 == 3526
      && tttLargeFiber70ParentOf 3526 == 2774
      && tttLargeFiber70ParentOf 2774 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block5Chunk3Sources 7 0 == 3399
      && tttLargeFiber70ParentOf 3399 == 3527
      && tttLargeFiber70ParentOf 3527 == 2775
      && tttLargeFiber70ParentOf 2775 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block5Chunk3Sources 8 0 == 3400
      && tttLargeFiber70ParentOf 3400 == 3528
      && tttLargeFiber70ParentOf 3528 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block5Chunk3Sources 9 0 == 3401
      && tttLargeFiber70ParentOf 3401 == 3529
      && tttLargeFiber70ParentOf 3529 == 2777
      && tttLargeFiber70ParentOf 2777 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block5Chunk3Sources 10 0 == 3402
      && tttLargeFiber70ParentOf 3402 == 3530
      && tttLargeFiber70ParentOf 3530 == 2778
      && tttLargeFiber70ParentOf 2778 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block5Chunk3Sources 11 0 == 3403
      && tttLargeFiber70ParentOf 3403 == 3531
      && tttLargeFiber70ParentOf 3531 == 2779
      && tttLargeFiber70ParentOf 2779 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block5Chunk3Sources 12 0 == 3404
      && tttLargeFiber70ParentOf 3404 == 3372
      && tttLargeFiber70ParentOf 3372 == 3344
      && tttLargeFiber70ParentOf 3344 == 3472
      && tttLargeFiber70ParentOf 3472 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block5Chunk3Sources 13 0 == 3405
      && tttLargeFiber70ParentOf 3405 == 3373
      && tttLargeFiber70ParentOf 3373 == 3345
      && tttLargeFiber70ParentOf 3345 == 3473
      && tttLargeFiber70ParentOf 3473 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block5Chunk3Sources 14 0 == 3406
      && tttLargeFiber70ParentOf 3406 == 3534
      && tttLargeFiber70ParentOf 3534 == 2782
      && tttLargeFiber70ParentOf 2782 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block5Chunk3Sources 15 0 == 3407
      && tttLargeFiber70ParentOf 3407 == 3535
      && tttLargeFiber70ParentOf 3535 == 2783
      && tttLargeFiber70ParentOf 2783 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block5Chunk3Row_0_ok :
    tttLargeFiber70Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_1_ok :
    tttLargeFiber70Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_2_ok :
    tttLargeFiber70Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_3_ok :
    tttLargeFiber70Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_4_ok :
    tttLargeFiber70Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_5_ok :
    tttLargeFiber70Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_6_ok :
    tttLargeFiber70Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_7_ok :
    tttLargeFiber70Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_8_ok :
    tttLargeFiber70Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_9_ok :
    tttLargeFiber70Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_10_ok :
    tttLargeFiber70Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_11_ok :
    tttLargeFiber70Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_12_ok :
    tttLargeFiber70Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_13_ok :
    tttLargeFiber70Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_14_ok :
    tttLargeFiber70Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3Row_15_ok :
    tttLargeFiber70Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_0_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_1_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_2_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_3_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_4_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_5_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_6_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_7_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_8_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_9_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_10_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_11_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_12_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_13_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_14_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentMap_15_ok :
    tttLargeFiber70Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_0_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_1_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_2_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_3_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_4_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_5_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_6_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_7_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_8_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_9_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_10_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_11_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_12_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_13_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_14_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block5Chunk3ParentPath_15_ok :
    tttLargeFiber70Block5Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber70Block5Chunk3RowCheck 0
    && tttLargeFiber70Block5Chunk3RowCheck 1
    && tttLargeFiber70Block5Chunk3RowCheck 2
    && tttLargeFiber70Block5Chunk3RowCheck 3
    && tttLargeFiber70Block5Chunk3RowCheck 4
    && tttLargeFiber70Block5Chunk3RowCheck 5
    && tttLargeFiber70Block5Chunk3RowCheck 6
    && tttLargeFiber70Block5Chunk3RowCheck 7
    && tttLargeFiber70Block5Chunk3RowCheck 8
    && tttLargeFiber70Block5Chunk3RowCheck 9
    && tttLargeFiber70Block5Chunk3RowCheck 10
    && tttLargeFiber70Block5Chunk3RowCheck 11
    && tttLargeFiber70Block5Chunk3RowCheck 12
    && tttLargeFiber70Block5Chunk3RowCheck 13
    && tttLargeFiber70Block5Chunk3RowCheck 14
    && tttLargeFiber70Block5Chunk3RowCheck 15

theorem tttLargeFiber70Block5Chunk3RowsAudit_ok :
    tttLargeFiber70Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber70Block5Chunk3RowsAudit,
    tttLargeFiber70Block5Chunk3Row_0_ok,
    tttLargeFiber70Block5Chunk3Row_1_ok,
    tttLargeFiber70Block5Chunk3Row_2_ok,
    tttLargeFiber70Block5Chunk3Row_3_ok,
    tttLargeFiber70Block5Chunk3Row_4_ok,
    tttLargeFiber70Block5Chunk3Row_5_ok,
    tttLargeFiber70Block5Chunk3Row_6_ok,
    tttLargeFiber70Block5Chunk3Row_7_ok,
    tttLargeFiber70Block5Chunk3Row_8_ok,
    tttLargeFiber70Block5Chunk3Row_9_ok,
    tttLargeFiber70Block5Chunk3Row_10_ok,
    tttLargeFiber70Block5Chunk3Row_11_ok,
    tttLargeFiber70Block5Chunk3Row_12_ok,
    tttLargeFiber70Block5Chunk3Row_13_ok,
    tttLargeFiber70Block5Chunk3Row_14_ok,
    tttLargeFiber70Block5Chunk3Row_15_ok]

def tttLargeFiber70Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber70Block5Chunk3ParentMapCheck 0
    && tttLargeFiber70Block5Chunk3ParentMapCheck 1
    && tttLargeFiber70Block5Chunk3ParentMapCheck 2
    && tttLargeFiber70Block5Chunk3ParentMapCheck 3
    && tttLargeFiber70Block5Chunk3ParentMapCheck 4
    && tttLargeFiber70Block5Chunk3ParentMapCheck 5
    && tttLargeFiber70Block5Chunk3ParentMapCheck 6
    && tttLargeFiber70Block5Chunk3ParentMapCheck 7
    && tttLargeFiber70Block5Chunk3ParentMapCheck 8
    && tttLargeFiber70Block5Chunk3ParentMapCheck 9
    && tttLargeFiber70Block5Chunk3ParentMapCheck 10
    && tttLargeFiber70Block5Chunk3ParentMapCheck 11
    && tttLargeFiber70Block5Chunk3ParentMapCheck 12
    && tttLargeFiber70Block5Chunk3ParentMapCheck 13
    && tttLargeFiber70Block5Chunk3ParentMapCheck 14
    && tttLargeFiber70Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber70Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber70Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber70Block5Chunk3ParentMapAudit,
    tttLargeFiber70Block5Chunk3ParentMap_0_ok,
    tttLargeFiber70Block5Chunk3ParentMap_1_ok,
    tttLargeFiber70Block5Chunk3ParentMap_2_ok,
    tttLargeFiber70Block5Chunk3ParentMap_3_ok,
    tttLargeFiber70Block5Chunk3ParentMap_4_ok,
    tttLargeFiber70Block5Chunk3ParentMap_5_ok,
    tttLargeFiber70Block5Chunk3ParentMap_6_ok,
    tttLargeFiber70Block5Chunk3ParentMap_7_ok,
    tttLargeFiber70Block5Chunk3ParentMap_8_ok,
    tttLargeFiber70Block5Chunk3ParentMap_9_ok,
    tttLargeFiber70Block5Chunk3ParentMap_10_ok,
    tttLargeFiber70Block5Chunk3ParentMap_11_ok,
    tttLargeFiber70Block5Chunk3ParentMap_12_ok,
    tttLargeFiber70Block5Chunk3ParentMap_13_ok,
    tttLargeFiber70Block5Chunk3ParentMap_14_ok,
    tttLargeFiber70Block5Chunk3ParentMap_15_ok]

def tttLargeFiber70Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber70Block5Chunk3ParentPathCheck 0
    && tttLargeFiber70Block5Chunk3ParentPathCheck 1
    && tttLargeFiber70Block5Chunk3ParentPathCheck 2
    && tttLargeFiber70Block5Chunk3ParentPathCheck 3
    && tttLargeFiber70Block5Chunk3ParentPathCheck 4
    && tttLargeFiber70Block5Chunk3ParentPathCheck 5
    && tttLargeFiber70Block5Chunk3ParentPathCheck 6
    && tttLargeFiber70Block5Chunk3ParentPathCheck 7
    && tttLargeFiber70Block5Chunk3ParentPathCheck 8
    && tttLargeFiber70Block5Chunk3ParentPathCheck 9
    && tttLargeFiber70Block5Chunk3ParentPathCheck 10
    && tttLargeFiber70Block5Chunk3ParentPathCheck 11
    && tttLargeFiber70Block5Chunk3ParentPathCheck 12
    && tttLargeFiber70Block5Chunk3ParentPathCheck 13
    && tttLargeFiber70Block5Chunk3ParentPathCheck 14
    && tttLargeFiber70Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber70Block5Chunk3ParentsAudit_ok :
    tttLargeFiber70Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber70Block5Chunk3ParentsAudit,
    tttLargeFiber70Block5Chunk3ParentPath_0_ok,
    tttLargeFiber70Block5Chunk3ParentPath_1_ok,
    tttLargeFiber70Block5Chunk3ParentPath_2_ok,
    tttLargeFiber70Block5Chunk3ParentPath_3_ok,
    tttLargeFiber70Block5Chunk3ParentPath_4_ok,
    tttLargeFiber70Block5Chunk3ParentPath_5_ok,
    tttLargeFiber70Block5Chunk3ParentPath_6_ok,
    tttLargeFiber70Block5Chunk3ParentPath_7_ok,
    tttLargeFiber70Block5Chunk3ParentPath_8_ok,
    tttLargeFiber70Block5Chunk3ParentPath_9_ok,
    tttLargeFiber70Block5Chunk3ParentPath_10_ok,
    tttLargeFiber70Block5Chunk3ParentPath_11_ok,
    tttLargeFiber70Block5Chunk3ParentPath_12_ok,
    tttLargeFiber70Block5Chunk3ParentPath_13_ok,
    tttLargeFiber70Block5Chunk3ParentPath_14_ok,
    tttLargeFiber70Block5Chunk3ParentPath_15_ok]

def tttLargeFiber70Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block5Chunk3SourcesCheck &&
    tttLargeFiber70Block5Chunk3RowsAudit &&
    tttLargeFiber70Block5Chunk3ParentMapAudit &&
    tttLargeFiber70Block5Chunk3ParentsAudit

theorem tttLargeFiber70Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber70Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block5Chunk3SourcesCheck_ok,
    tttLargeFiber70Block5Chunk3RowsAudit_ok,
    tttLargeFiber70Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber70Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
