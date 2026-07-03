import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 6 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block6Chunk1Sources : List Nat :=
  [   5600, 5601, 5602, 5603, 5604, 5605, 5606, 5607,
   5608, 5609, 5610, 5611, 5612, 5613, 5614, 5615]

def tttLargeFiber44Row400 : TripleComponentParentRow :=
  tripleRow 5600 5584 166 66 16 166 64 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row401 : TripleComponentParentRow :=
  tripleRow 5601 5585 166 66 17 166 64 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row402 : TripleComponentParentRow :=
  tripleRow 5602 5586 166 66 18 166 64 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row403 : TripleComponentParentRow :=
  tripleRow 5603 5587 166 66 19 166 64 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row404 : TripleComponentParentRow :=
  tripleRow 5604 5588 166 66 32 166 64 100
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

def tttLargeFiber44Row405 : TripleComponentParentRow :=
  tripleRow 5605 5589 166 66 33 166 64 101
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

def tttLargeFiber44Row406 : TripleComponentParentRow :=
  tripleRow 5606 5590 166 66 34 166 64 102
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

def tttLargeFiber44Row407 : TripleComponentParentRow :=
  tripleRow 5607 5591 166 66 35 166 64 103
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

def tttLargeFiber44Row408 : TripleComponentParentRow :=
  tripleRow 5608 5592 166 67 24 166 65 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row409 : TripleComponentParentRow :=
  tripleRow 5609 5593 166 67 25 166 65 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row410 : TripleComponentParentRow :=
  tripleRow 5610 5482 166 67 26 164 135 10
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

def tttLargeFiber44Row411 : TripleComponentParentRow :=
  tripleRow 5611 5483 166 67 27 164 135 11
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

def tttLargeFiber44Row412 : TripleComponentParentRow :=
  tripleRow 5612 5484 166 67 40 164 135 56
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

def tttLargeFiber44Row413 : TripleComponentParentRow :=
  tripleRow 5613 5485 166 67 41 164 135 57
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

def tttLargeFiber44Row414 : TripleComponentParentRow :=
  tripleRow 5614 5486 166 67 42 164 135 58
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

def tttLargeFiber44Row415 : TripleComponentParentRow :=
  tripleRow 5615 5487 166 67 43 164 135 59
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

def tttLargeFiber44Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row400
  , tttLargeFiber44Row401
  , tttLargeFiber44Row402
  , tttLargeFiber44Row403
  , tttLargeFiber44Row404
  , tttLargeFiber44Row405
  , tttLargeFiber44Row406
  , tttLargeFiber44Row407
  , tttLargeFiber44Row408
  , tttLargeFiber44Row409
  , tttLargeFiber44Row410
  , tttLargeFiber44Row411
  , tttLargeFiber44Row412
  , tttLargeFiber44Row413
  , tttLargeFiber44Row414
  , tttLargeFiber44Row415
  ]

def tttLargeFiber44Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber44Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber44Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber44Block6Chunk1Sources

theorem tttLargeFiber44Block6Chunk1SourcesCheck_ok :
    tttLargeFiber44Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber44Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block6Chunk1RowValid
    (listGetD tttLargeFiber44Block6Chunk1Rows i default)

def tttLargeFiber44Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block6Chunk1Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block6Chunk1Sources 0 0 == 5600
      && tttLargeFiber44ParentOf 5600 == 5584
      && tttLargeFiber44ParentOf 5584 == 5456
      && tttLargeFiber44ParentOf 5456 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block6Chunk1Sources 1 0 == 5601
      && tttLargeFiber44ParentOf 5601 == 5585
      && tttLargeFiber44ParentOf 5585 == 5457
      && tttLargeFiber44ParentOf 5457 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block6Chunk1Sources 2 0 == 5602
      && tttLargeFiber44ParentOf 5602 == 5586
      && tttLargeFiber44ParentOf 5586 == 5584
      && tttLargeFiber44ParentOf 5584 == 5456
      && tttLargeFiber44ParentOf 5456 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block6Chunk1Sources 3 0 == 5603
      && tttLargeFiber44ParentOf 5603 == 5587
      && tttLargeFiber44ParentOf 5587 == 5459
      && tttLargeFiber44ParentOf 5459 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block6Chunk1Sources 4 0 == 5604
      && tttLargeFiber44ParentOf 5604 == 5588
      && tttLargeFiber44ParentOf 5588 == 5460
      && tttLargeFiber44ParentOf 5460 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block6Chunk1Sources 5 0 == 5605
      && tttLargeFiber44ParentOf 5605 == 5589
      && tttLargeFiber44ParentOf 5589 == 5461
      && tttLargeFiber44ParentOf 5461 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block6Chunk1Sources 6 0 == 5606
      && tttLargeFiber44ParentOf 5606 == 5590
      && tttLargeFiber44ParentOf 5590 == 5585
      && tttLargeFiber44ParentOf 5585 == 5457
      && tttLargeFiber44ParentOf 5457 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block6Chunk1Sources 7 0 == 5607
      && tttLargeFiber44ParentOf 5607 == 5591
      && tttLargeFiber44ParentOf 5591 == 5584
      && tttLargeFiber44ParentOf 5584 == 5456
      && tttLargeFiber44ParentOf 5456 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block6Chunk1Sources 8 0 == 5608
      && tttLargeFiber44ParentOf 5608 == 5592
      && tttLargeFiber44ParentOf 5592 == 5464
      && tttLargeFiber44ParentOf 5464 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block6Chunk1Sources 9 0 == 5609
      && tttLargeFiber44ParentOf 5609 == 5593
      && tttLargeFiber44ParentOf 5593 == 5465
      && tttLargeFiber44ParentOf 5465 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block6Chunk1Sources 10 0 == 5610
      && tttLargeFiber44ParentOf 5610 == 5482
      && tttLargeFiber44ParentOf 5482 == 4938
      && tttLargeFiber44ParentOf 4938 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block6Chunk1Sources 11 0 == 5611
      && tttLargeFiber44ParentOf 5611 == 5483
      && tttLargeFiber44ParentOf 5483 == 4939
      && tttLargeFiber44ParentOf 4939 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block6Chunk1Sources 12 0 == 5612
      && tttLargeFiber44ParentOf 5612 == 5484
      && tttLargeFiber44ParentOf 5484 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block6Chunk1Sources 13 0 == 5613
      && tttLargeFiber44ParentOf 5613 == 5485
      && tttLargeFiber44ParentOf 5485 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block6Chunk1Sources 14 0 == 5614
      && tttLargeFiber44ParentOf 5614 == 5486
      && tttLargeFiber44ParentOf 5486 == 4942
      && tttLargeFiber44ParentOf 4942 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block6Chunk1Sources 15 0 == 5615
      && tttLargeFiber44ParentOf 5615 == 5487
      && tttLargeFiber44ParentOf 5487 == 4943
      && tttLargeFiber44ParentOf 4943 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block6Chunk1Row_0_ok :
    tttLargeFiber44Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_1_ok :
    tttLargeFiber44Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_2_ok :
    tttLargeFiber44Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_3_ok :
    tttLargeFiber44Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_4_ok :
    tttLargeFiber44Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_5_ok :
    tttLargeFiber44Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_6_ok :
    tttLargeFiber44Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_7_ok :
    tttLargeFiber44Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_8_ok :
    tttLargeFiber44Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_9_ok :
    tttLargeFiber44Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_10_ok :
    tttLargeFiber44Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_11_ok :
    tttLargeFiber44Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_12_ok :
    tttLargeFiber44Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_13_ok :
    tttLargeFiber44Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_14_ok :
    tttLargeFiber44Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1Row_15_ok :
    tttLargeFiber44Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_0_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_1_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_2_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_3_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_4_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_5_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_6_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_7_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_8_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_9_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_10_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_11_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_12_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_13_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_14_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentMap_15_ok :
    tttLargeFiber44Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_0_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_1_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_2_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_3_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_4_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_5_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_6_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_7_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_8_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_9_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_10_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_11_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_12_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_13_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_14_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block6Chunk1ParentPath_15_ok :
    tttLargeFiber44Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber44Block6Chunk1RowCheck 0
    && tttLargeFiber44Block6Chunk1RowCheck 1
    && tttLargeFiber44Block6Chunk1RowCheck 2
    && tttLargeFiber44Block6Chunk1RowCheck 3
    && tttLargeFiber44Block6Chunk1RowCheck 4
    && tttLargeFiber44Block6Chunk1RowCheck 5
    && tttLargeFiber44Block6Chunk1RowCheck 6
    && tttLargeFiber44Block6Chunk1RowCheck 7
    && tttLargeFiber44Block6Chunk1RowCheck 8
    && tttLargeFiber44Block6Chunk1RowCheck 9
    && tttLargeFiber44Block6Chunk1RowCheck 10
    && tttLargeFiber44Block6Chunk1RowCheck 11
    && tttLargeFiber44Block6Chunk1RowCheck 12
    && tttLargeFiber44Block6Chunk1RowCheck 13
    && tttLargeFiber44Block6Chunk1RowCheck 14
    && tttLargeFiber44Block6Chunk1RowCheck 15

theorem tttLargeFiber44Block6Chunk1RowsAudit_ok :
    tttLargeFiber44Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber44Block6Chunk1RowsAudit,
    tttLargeFiber44Block6Chunk1Row_0_ok,
    tttLargeFiber44Block6Chunk1Row_1_ok,
    tttLargeFiber44Block6Chunk1Row_2_ok,
    tttLargeFiber44Block6Chunk1Row_3_ok,
    tttLargeFiber44Block6Chunk1Row_4_ok,
    tttLargeFiber44Block6Chunk1Row_5_ok,
    tttLargeFiber44Block6Chunk1Row_6_ok,
    tttLargeFiber44Block6Chunk1Row_7_ok,
    tttLargeFiber44Block6Chunk1Row_8_ok,
    tttLargeFiber44Block6Chunk1Row_9_ok,
    tttLargeFiber44Block6Chunk1Row_10_ok,
    tttLargeFiber44Block6Chunk1Row_11_ok,
    tttLargeFiber44Block6Chunk1Row_12_ok,
    tttLargeFiber44Block6Chunk1Row_13_ok,
    tttLargeFiber44Block6Chunk1Row_14_ok,
    tttLargeFiber44Block6Chunk1Row_15_ok]

def tttLargeFiber44Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber44Block6Chunk1ParentMapCheck 0
    && tttLargeFiber44Block6Chunk1ParentMapCheck 1
    && tttLargeFiber44Block6Chunk1ParentMapCheck 2
    && tttLargeFiber44Block6Chunk1ParentMapCheck 3
    && tttLargeFiber44Block6Chunk1ParentMapCheck 4
    && tttLargeFiber44Block6Chunk1ParentMapCheck 5
    && tttLargeFiber44Block6Chunk1ParentMapCheck 6
    && tttLargeFiber44Block6Chunk1ParentMapCheck 7
    && tttLargeFiber44Block6Chunk1ParentMapCheck 8
    && tttLargeFiber44Block6Chunk1ParentMapCheck 9
    && tttLargeFiber44Block6Chunk1ParentMapCheck 10
    && tttLargeFiber44Block6Chunk1ParentMapCheck 11
    && tttLargeFiber44Block6Chunk1ParentMapCheck 12
    && tttLargeFiber44Block6Chunk1ParentMapCheck 13
    && tttLargeFiber44Block6Chunk1ParentMapCheck 14
    && tttLargeFiber44Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber44Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber44Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber44Block6Chunk1ParentMapAudit,
    tttLargeFiber44Block6Chunk1ParentMap_0_ok,
    tttLargeFiber44Block6Chunk1ParentMap_1_ok,
    tttLargeFiber44Block6Chunk1ParentMap_2_ok,
    tttLargeFiber44Block6Chunk1ParentMap_3_ok,
    tttLargeFiber44Block6Chunk1ParentMap_4_ok,
    tttLargeFiber44Block6Chunk1ParentMap_5_ok,
    tttLargeFiber44Block6Chunk1ParentMap_6_ok,
    tttLargeFiber44Block6Chunk1ParentMap_7_ok,
    tttLargeFiber44Block6Chunk1ParentMap_8_ok,
    tttLargeFiber44Block6Chunk1ParentMap_9_ok,
    tttLargeFiber44Block6Chunk1ParentMap_10_ok,
    tttLargeFiber44Block6Chunk1ParentMap_11_ok,
    tttLargeFiber44Block6Chunk1ParentMap_12_ok,
    tttLargeFiber44Block6Chunk1ParentMap_13_ok,
    tttLargeFiber44Block6Chunk1ParentMap_14_ok,
    tttLargeFiber44Block6Chunk1ParentMap_15_ok]

def tttLargeFiber44Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber44Block6Chunk1ParentPathCheck 0
    && tttLargeFiber44Block6Chunk1ParentPathCheck 1
    && tttLargeFiber44Block6Chunk1ParentPathCheck 2
    && tttLargeFiber44Block6Chunk1ParentPathCheck 3
    && tttLargeFiber44Block6Chunk1ParentPathCheck 4
    && tttLargeFiber44Block6Chunk1ParentPathCheck 5
    && tttLargeFiber44Block6Chunk1ParentPathCheck 6
    && tttLargeFiber44Block6Chunk1ParentPathCheck 7
    && tttLargeFiber44Block6Chunk1ParentPathCheck 8
    && tttLargeFiber44Block6Chunk1ParentPathCheck 9
    && tttLargeFiber44Block6Chunk1ParentPathCheck 10
    && tttLargeFiber44Block6Chunk1ParentPathCheck 11
    && tttLargeFiber44Block6Chunk1ParentPathCheck 12
    && tttLargeFiber44Block6Chunk1ParentPathCheck 13
    && tttLargeFiber44Block6Chunk1ParentPathCheck 14
    && tttLargeFiber44Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber44Block6Chunk1ParentsAudit_ok :
    tttLargeFiber44Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber44Block6Chunk1ParentsAudit,
    tttLargeFiber44Block6Chunk1ParentPath_0_ok,
    tttLargeFiber44Block6Chunk1ParentPath_1_ok,
    tttLargeFiber44Block6Chunk1ParentPath_2_ok,
    tttLargeFiber44Block6Chunk1ParentPath_3_ok,
    tttLargeFiber44Block6Chunk1ParentPath_4_ok,
    tttLargeFiber44Block6Chunk1ParentPath_5_ok,
    tttLargeFiber44Block6Chunk1ParentPath_6_ok,
    tttLargeFiber44Block6Chunk1ParentPath_7_ok,
    tttLargeFiber44Block6Chunk1ParentPath_8_ok,
    tttLargeFiber44Block6Chunk1ParentPath_9_ok,
    tttLargeFiber44Block6Chunk1ParentPath_10_ok,
    tttLargeFiber44Block6Chunk1ParentPath_11_ok,
    tttLargeFiber44Block6Chunk1ParentPath_12_ok,
    tttLargeFiber44Block6Chunk1ParentPath_13_ok,
    tttLargeFiber44Block6Chunk1ParentPath_14_ok,
    tttLargeFiber44Block6Chunk1ParentPath_15_ok]

def tttLargeFiber44Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block6Chunk1SourcesCheck &&
    tttLargeFiber44Block6Chunk1RowsAudit &&
    tttLargeFiber44Block6Chunk1ParentMapAudit &&
    tttLargeFiber44Block6Chunk1ParentsAudit

theorem tttLargeFiber44Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber44Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block6Chunk1SourcesCheck_ok,
    tttLargeFiber44Block6Chunk1RowsAudit_ok,
    tttLargeFiber44Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber44Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
