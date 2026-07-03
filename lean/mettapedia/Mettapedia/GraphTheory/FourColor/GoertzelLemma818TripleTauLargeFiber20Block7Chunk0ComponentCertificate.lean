import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 7 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block7Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block7Chunk0Sources : List Nat :=
  [   6464, 6465, 6466, 6467, 6468, 6469, 6470, 6471,
   6472, 6473, 6474, 6475, 6476, 6477, 6478, 6479]

def tttLargeFiber20Row448 : TripleComponentParentRow :=
  tripleRow 6464 6336 191 72 80 189 140 148
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row449 : TripleComponentParentRow :=
  tripleRow 6465 6337 191 72 81 189 140 149
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row450 : TripleComponentParentRow :=
  tripleRow 6466 6464 191 72 82 191 72 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row451 : TripleComponentParentRow :=
  tripleRow 6467 6339 191 72 83 189 140 151
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row452 : TripleComponentParentRow :=
  tripleRow 6468 6340 191 72 100 189 140 164
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row453 : TripleComponentParentRow :=
  tripleRow 6469 6341 191 72 101 189 140 165
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row454 : TripleComponentParentRow :=
  tripleRow 6470 6465 191 72 102 191 72 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row455 : TripleComponentParentRow :=
  tripleRow 6471 6464 191 72 103 191 72 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row456 : TripleComponentParentRow :=
  tripleRow 6472 6344 191 73 88 189 141 156
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row457 : TripleComponentParentRow :=
  tripleRow 6473 6345 191 73 89 189 141 157
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row458 : TripleComponentParentRow :=
  tripleRow 6474 6472 191 73 90 191 73 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row459 : TripleComponentParentRow :=
  tripleRow 6475 6347 191 73 91 189 141 159
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row460 : TripleComponentParentRow :=
  tripleRow 6476 6348 191 73 108 189 141 172
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row461 : TripleComponentParentRow :=
  tripleRow 6477 6349 191 73 109 189 141 173
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row462 : TripleComponentParentRow :=
  tripleRow 6478 6473 191 73 110 191 73 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row463 : TripleComponentParentRow :=
  tripleRow 6479 6472 191 73 111 191 73 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Block7Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row448
  , tttLargeFiber20Row449
  , tttLargeFiber20Row450
  , tttLargeFiber20Row451
  , tttLargeFiber20Row452
  , tttLargeFiber20Row453
  , tttLargeFiber20Row454
  , tttLargeFiber20Row455
  , tttLargeFiber20Row456
  , tttLargeFiber20Row457
  , tttLargeFiber20Row458
  , tttLargeFiber20Row459
  , tttLargeFiber20Row460
  , tttLargeFiber20Row461
  , tttLargeFiber20Row462
  , tttLargeFiber20Row463
  ]

def tttLargeFiber20Block7Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block7Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block7Chunk0ExpectedContains row.source &&
    tttLargeFiber20Block7Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block7Chunk0SourcesCheck : Bool :=
  (tttLargeFiber20Block7Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber20Block7Chunk0Sources

theorem tttLargeFiber20Block7Chunk0SourcesCheck_ok :
    tttLargeFiber20Block7Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber20Block7Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block7Chunk0RowValid
    (listGetD tttLargeFiber20Block7Chunk0Rows i default)

def tttLargeFiber20Block7Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block7Chunk0Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block7Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block7Chunk0Sources 0 0 == 6464
      && tttLargeFiber20ParentOf 6464 == 6336
      && tttLargeFiber20ParentOf 6336 == 4704
      && tttLargeFiber20ParentOf 4704 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block7Chunk0Sources 1 0 == 6465
      && tttLargeFiber20ParentOf 6465 == 6337
      && tttLargeFiber20ParentOf 6337 == 4705
      && tttLargeFiber20ParentOf 4705 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block7Chunk0Sources 2 0 == 6466
      && tttLargeFiber20ParentOf 6466 == 6464
      && tttLargeFiber20ParentOf 6464 == 6336
      && tttLargeFiber20ParentOf 6336 == 4704
      && tttLargeFiber20ParentOf 4704 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block7Chunk0Sources 3 0 == 6467
      && tttLargeFiber20ParentOf 6467 == 6339
      && tttLargeFiber20ParentOf 6339 == 4707
      && tttLargeFiber20ParentOf 4707 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block7Chunk0Sources 4 0 == 6468
      && tttLargeFiber20ParentOf 6468 == 6340
      && tttLargeFiber20ParentOf 6340 == 4708
      && tttLargeFiber20ParentOf 4708 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block7Chunk0Sources 5 0 == 6469
      && tttLargeFiber20ParentOf 6469 == 6341
      && tttLargeFiber20ParentOf 6341 == 4709
      && tttLargeFiber20ParentOf 4709 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block7Chunk0Sources 6 0 == 6470
      && tttLargeFiber20ParentOf 6470 == 6465
      && tttLargeFiber20ParentOf 6465 == 6337
      && tttLargeFiber20ParentOf 6337 == 4705
      && tttLargeFiber20ParentOf 4705 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block7Chunk0Sources 7 0 == 6471
      && tttLargeFiber20ParentOf 6471 == 6464
      && tttLargeFiber20ParentOf 6464 == 6336
      && tttLargeFiber20ParentOf 6336 == 4704
      && tttLargeFiber20ParentOf 4704 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block7Chunk0Sources 8 0 == 6472
      && tttLargeFiber20ParentOf 6472 == 6344
      && tttLargeFiber20ParentOf 6344 == 4712
      && tttLargeFiber20ParentOf 4712 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block7Chunk0Sources 9 0 == 6473
      && tttLargeFiber20ParentOf 6473 == 6345
      && tttLargeFiber20ParentOf 6345 == 4713
      && tttLargeFiber20ParentOf 4713 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block7Chunk0Sources 10 0 == 6474
      && tttLargeFiber20ParentOf 6474 == 6472
      && tttLargeFiber20ParentOf 6472 == 6344
      && tttLargeFiber20ParentOf 6344 == 4712
      && tttLargeFiber20ParentOf 4712 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block7Chunk0Sources 11 0 == 6475
      && tttLargeFiber20ParentOf 6475 == 6347
      && tttLargeFiber20ParentOf 6347 == 4715
      && tttLargeFiber20ParentOf 4715 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block7Chunk0Sources 12 0 == 6476
      && tttLargeFiber20ParentOf 6476 == 6348
      && tttLargeFiber20ParentOf 6348 == 4716
      && tttLargeFiber20ParentOf 4716 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block7Chunk0Sources 13 0 == 6477
      && tttLargeFiber20ParentOf 6477 == 6349
      && tttLargeFiber20ParentOf 6349 == 4717
      && tttLargeFiber20ParentOf 4717 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (6 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block7Chunk0Sources 14 0 == 6478
      && tttLargeFiber20ParentOf 6478 == 6473
      && tttLargeFiber20ParentOf 6473 == 6345
      && tttLargeFiber20ParentOf 6345 == 4713
      && tttLargeFiber20ParentOf 4713 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (6 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block7Chunk0Sources 15 0 == 6479
      && tttLargeFiber20ParentOf 6479 == 6472
      && tttLargeFiber20ParentOf 6472 == 6344
      && tttLargeFiber20ParentOf 6344 == 4712
      && tttLargeFiber20ParentOf 4712 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block7Chunk0Row_0_ok :
    tttLargeFiber20Block7Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_1_ok :
    tttLargeFiber20Block7Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_2_ok :
    tttLargeFiber20Block7Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_3_ok :
    tttLargeFiber20Block7Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_4_ok :
    tttLargeFiber20Block7Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_5_ok :
    tttLargeFiber20Block7Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_6_ok :
    tttLargeFiber20Block7Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_7_ok :
    tttLargeFiber20Block7Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_8_ok :
    tttLargeFiber20Block7Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_9_ok :
    tttLargeFiber20Block7Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_10_ok :
    tttLargeFiber20Block7Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_11_ok :
    tttLargeFiber20Block7Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_12_ok :
    tttLargeFiber20Block7Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_13_ok :
    tttLargeFiber20Block7Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_14_ok :
    tttLargeFiber20Block7Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0Row_15_ok :
    tttLargeFiber20Block7Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_0_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_1_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_2_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_3_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_4_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_5_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_6_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_7_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_8_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_9_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_10_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_11_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_12_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_13_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_14_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentMap_15_ok :
    tttLargeFiber20Block7Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_0_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_1_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_2_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_3_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_4_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_5_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_6_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_7_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_8_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_9_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_10_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_11_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_12_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_13_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_14_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block7Chunk0ParentPath_15_ok :
    tttLargeFiber20Block7Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block7Chunk0RowsAudit : Bool :=
  tttLargeFiber20Block7Chunk0RowCheck 0
    && tttLargeFiber20Block7Chunk0RowCheck 1
    && tttLargeFiber20Block7Chunk0RowCheck 2
    && tttLargeFiber20Block7Chunk0RowCheck 3
    && tttLargeFiber20Block7Chunk0RowCheck 4
    && tttLargeFiber20Block7Chunk0RowCheck 5
    && tttLargeFiber20Block7Chunk0RowCheck 6
    && tttLargeFiber20Block7Chunk0RowCheck 7
    && tttLargeFiber20Block7Chunk0RowCheck 8
    && tttLargeFiber20Block7Chunk0RowCheck 9
    && tttLargeFiber20Block7Chunk0RowCheck 10
    && tttLargeFiber20Block7Chunk0RowCheck 11
    && tttLargeFiber20Block7Chunk0RowCheck 12
    && tttLargeFiber20Block7Chunk0RowCheck 13
    && tttLargeFiber20Block7Chunk0RowCheck 14
    && tttLargeFiber20Block7Chunk0RowCheck 15

theorem tttLargeFiber20Block7Chunk0RowsAudit_ok :
    tttLargeFiber20Block7Chunk0RowsAudit = true := by
  simp [tttLargeFiber20Block7Chunk0RowsAudit,
    tttLargeFiber20Block7Chunk0Row_0_ok,
    tttLargeFiber20Block7Chunk0Row_1_ok,
    tttLargeFiber20Block7Chunk0Row_2_ok,
    tttLargeFiber20Block7Chunk0Row_3_ok,
    tttLargeFiber20Block7Chunk0Row_4_ok,
    tttLargeFiber20Block7Chunk0Row_5_ok,
    tttLargeFiber20Block7Chunk0Row_6_ok,
    tttLargeFiber20Block7Chunk0Row_7_ok,
    tttLargeFiber20Block7Chunk0Row_8_ok,
    tttLargeFiber20Block7Chunk0Row_9_ok,
    tttLargeFiber20Block7Chunk0Row_10_ok,
    tttLargeFiber20Block7Chunk0Row_11_ok,
    tttLargeFiber20Block7Chunk0Row_12_ok,
    tttLargeFiber20Block7Chunk0Row_13_ok,
    tttLargeFiber20Block7Chunk0Row_14_ok,
    tttLargeFiber20Block7Chunk0Row_15_ok]

def tttLargeFiber20Block7Chunk0ParentMapAudit : Bool :=
  tttLargeFiber20Block7Chunk0ParentMapCheck 0
    && tttLargeFiber20Block7Chunk0ParentMapCheck 1
    && tttLargeFiber20Block7Chunk0ParentMapCheck 2
    && tttLargeFiber20Block7Chunk0ParentMapCheck 3
    && tttLargeFiber20Block7Chunk0ParentMapCheck 4
    && tttLargeFiber20Block7Chunk0ParentMapCheck 5
    && tttLargeFiber20Block7Chunk0ParentMapCheck 6
    && tttLargeFiber20Block7Chunk0ParentMapCheck 7
    && tttLargeFiber20Block7Chunk0ParentMapCheck 8
    && tttLargeFiber20Block7Chunk0ParentMapCheck 9
    && tttLargeFiber20Block7Chunk0ParentMapCheck 10
    && tttLargeFiber20Block7Chunk0ParentMapCheck 11
    && tttLargeFiber20Block7Chunk0ParentMapCheck 12
    && tttLargeFiber20Block7Chunk0ParentMapCheck 13
    && tttLargeFiber20Block7Chunk0ParentMapCheck 14
    && tttLargeFiber20Block7Chunk0ParentMapCheck 15

theorem tttLargeFiber20Block7Chunk0ParentMapAudit_ok :
    tttLargeFiber20Block7Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber20Block7Chunk0ParentMapAudit,
    tttLargeFiber20Block7Chunk0ParentMap_0_ok,
    tttLargeFiber20Block7Chunk0ParentMap_1_ok,
    tttLargeFiber20Block7Chunk0ParentMap_2_ok,
    tttLargeFiber20Block7Chunk0ParentMap_3_ok,
    tttLargeFiber20Block7Chunk0ParentMap_4_ok,
    tttLargeFiber20Block7Chunk0ParentMap_5_ok,
    tttLargeFiber20Block7Chunk0ParentMap_6_ok,
    tttLargeFiber20Block7Chunk0ParentMap_7_ok,
    tttLargeFiber20Block7Chunk0ParentMap_8_ok,
    tttLargeFiber20Block7Chunk0ParentMap_9_ok,
    tttLargeFiber20Block7Chunk0ParentMap_10_ok,
    tttLargeFiber20Block7Chunk0ParentMap_11_ok,
    tttLargeFiber20Block7Chunk0ParentMap_12_ok,
    tttLargeFiber20Block7Chunk0ParentMap_13_ok,
    tttLargeFiber20Block7Chunk0ParentMap_14_ok,
    tttLargeFiber20Block7Chunk0ParentMap_15_ok]

def tttLargeFiber20Block7Chunk0ParentsAudit : Bool :=
  tttLargeFiber20Block7Chunk0ParentPathCheck 0
    && tttLargeFiber20Block7Chunk0ParentPathCheck 1
    && tttLargeFiber20Block7Chunk0ParentPathCheck 2
    && tttLargeFiber20Block7Chunk0ParentPathCheck 3
    && tttLargeFiber20Block7Chunk0ParentPathCheck 4
    && tttLargeFiber20Block7Chunk0ParentPathCheck 5
    && tttLargeFiber20Block7Chunk0ParentPathCheck 6
    && tttLargeFiber20Block7Chunk0ParentPathCheck 7
    && tttLargeFiber20Block7Chunk0ParentPathCheck 8
    && tttLargeFiber20Block7Chunk0ParentPathCheck 9
    && tttLargeFiber20Block7Chunk0ParentPathCheck 10
    && tttLargeFiber20Block7Chunk0ParentPathCheck 11
    && tttLargeFiber20Block7Chunk0ParentPathCheck 12
    && tttLargeFiber20Block7Chunk0ParentPathCheck 13
    && tttLargeFiber20Block7Chunk0ParentPathCheck 14
    && tttLargeFiber20Block7Chunk0ParentPathCheck 15

theorem tttLargeFiber20Block7Chunk0ParentsAudit_ok :
    tttLargeFiber20Block7Chunk0ParentsAudit = true := by
  simp [tttLargeFiber20Block7Chunk0ParentsAudit,
    tttLargeFiber20Block7Chunk0ParentPath_0_ok,
    tttLargeFiber20Block7Chunk0ParentPath_1_ok,
    tttLargeFiber20Block7Chunk0ParentPath_2_ok,
    tttLargeFiber20Block7Chunk0ParentPath_3_ok,
    tttLargeFiber20Block7Chunk0ParentPath_4_ok,
    tttLargeFiber20Block7Chunk0ParentPath_5_ok,
    tttLargeFiber20Block7Chunk0ParentPath_6_ok,
    tttLargeFiber20Block7Chunk0ParentPath_7_ok,
    tttLargeFiber20Block7Chunk0ParentPath_8_ok,
    tttLargeFiber20Block7Chunk0ParentPath_9_ok,
    tttLargeFiber20Block7Chunk0ParentPath_10_ok,
    tttLargeFiber20Block7Chunk0ParentPath_11_ok,
    tttLargeFiber20Block7Chunk0ParentPath_12_ok,
    tttLargeFiber20Block7Chunk0ParentPath_13_ok,
    tttLargeFiber20Block7Chunk0ParentPath_14_ok,
    tttLargeFiber20Block7Chunk0ParentPath_15_ok]

def tttLargeFiber20Block7Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block7Chunk0SourcesCheck &&
    tttLargeFiber20Block7Chunk0RowsAudit &&
    tttLargeFiber20Block7Chunk0ParentMapAudit &&
    tttLargeFiber20Block7Chunk0ParentsAudit

theorem tttLargeFiber20Block7Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber20Block7Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block7Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block7Chunk0SourcesCheck_ok,
    tttLargeFiber20Block7Chunk0RowsAudit_ok,
    tttLargeFiber20Block7Chunk0ParentMapAudit_ok,
    tttLargeFiber20Block7Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block7Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
