import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block1Chunk1Sources : List Nat :=
  [   624, 625, 626, 627, 628, 629, 630, 631,
   632, 633, 634, 635, 636, 637, 638, 639]

def tttLargeFiber60Row80 : TripleComponentParentRow :=
  tripleRow 624 560 17 90 16 16 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row81 : TripleComponentParentRow :=
  tripleRow 625 561 17 90 17 16 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row82 : TripleComponentParentRow :=
  tripleRow 626 562 17 90 18 16 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row83 : TripleComponentParentRow :=
  tripleRow 627 563 17 90 19 16 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row84 : TripleComponentParentRow :=
  tripleRow 628 564 17 90 32 16 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row85 : TripleComponentParentRow :=
  tripleRow 629 565 17 90 33 16 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row86 : TripleComponentParentRow :=
  tripleRow 630 566 17 90 34 16 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row87 : TripleComponentParentRow :=
  tripleRow 631 567 17 90 35 16 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row88 : TripleComponentParentRow :=
  tripleRow 632 568 17 91 24 16 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row89 : TripleComponentParentRow :=
  tripleRow 633 569 17 91 25 16 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row90 : TripleComponentParentRow :=
  tripleRow 634 570 17 91 26 16 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row91 : TripleComponentParentRow :=
  tripleRow 635 571 17 91 27 16 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row92 : TripleComponentParentRow :=
  tripleRow 636 572 17 91 40 16 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row93 : TripleComponentParentRow :=
  tripleRow 637 573 17 91 41 16 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row94 : TripleComponentParentRow :=
  tripleRow 638 574 17 91 42 16 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row95 : TripleComponentParentRow :=
  tripleRow 639 575 17 91 43 16 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row80
  , tttLargeFiber60Row81
  , tttLargeFiber60Row82
  , tttLargeFiber60Row83
  , tttLargeFiber60Row84
  , tttLargeFiber60Row85
  , tttLargeFiber60Row86
  , tttLargeFiber60Row87
  , tttLargeFiber60Row88
  , tttLargeFiber60Row89
  , tttLargeFiber60Row90
  , tttLargeFiber60Row91
  , tttLargeFiber60Row92
  , tttLargeFiber60Row93
  , tttLargeFiber60Row94
  , tttLargeFiber60Row95
  ]

def tttLargeFiber60Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber60Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber60Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber60Block1Chunk1Sources

theorem tttLargeFiber60Block1Chunk1SourcesCheck_ok :
    tttLargeFiber60Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber60Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block1Chunk1RowValid
    (listGetD tttLargeFiber60Block1Chunk1Rows i default)

def tttLargeFiber60Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block1Chunk1Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block1Chunk1Sources 0 0 == 624
      && tttLargeFiber60ParentOf 624 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block1Chunk1Sources 1 0 == 625
      && tttLargeFiber60ParentOf 625 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block1Chunk1Sources 2 0 == 626
      && tttLargeFiber60ParentOf 626 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block1Chunk1Sources 3 0 == 627
      && tttLargeFiber60ParentOf 627 == 563
      && tttLargeFiber60ParentOf 563 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block1Chunk1Sources 4 0 == 628
      && tttLargeFiber60ParentOf 628 == 564
      && tttLargeFiber60ParentOf 564 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block1Chunk1Sources 5 0 == 629
      && tttLargeFiber60ParentOf 629 == 565
      && tttLargeFiber60ParentOf 565 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block1Chunk1Sources 6 0 == 630
      && tttLargeFiber60ParentOf 630 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block1Chunk1Sources 7 0 == 631
      && tttLargeFiber60ParentOf 631 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block1Chunk1Sources 8 0 == 632
      && tttLargeFiber60ParentOf 632 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block1Chunk1Sources 9 0 == 633
      && tttLargeFiber60ParentOf 633 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block1Chunk1Sources 10 0 == 634
      && tttLargeFiber60ParentOf 634 == 570
      && tttLargeFiber60ParentOf 570 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block1Chunk1Sources 11 0 == 635
      && tttLargeFiber60ParentOf 635 == 571
      && tttLargeFiber60ParentOf 571 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block1Chunk1Sources 12 0 == 636
      && tttLargeFiber60ParentOf 636 == 572
      && tttLargeFiber60ParentOf 572 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block1Chunk1Sources 13 0 == 637
      && tttLargeFiber60ParentOf 637 == 573
      && tttLargeFiber60ParentOf 573 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block1Chunk1Sources 14 0 == 638
      && tttLargeFiber60ParentOf 638 == 574
      && tttLargeFiber60ParentOf 574 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block1Chunk1Sources 15 0 == 639
      && tttLargeFiber60ParentOf 639 == 575
      && tttLargeFiber60ParentOf 575 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block1Chunk1Row_0_ok :
    tttLargeFiber60Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_1_ok :
    tttLargeFiber60Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_2_ok :
    tttLargeFiber60Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_3_ok :
    tttLargeFiber60Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_4_ok :
    tttLargeFiber60Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_5_ok :
    tttLargeFiber60Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_6_ok :
    tttLargeFiber60Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_7_ok :
    tttLargeFiber60Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_8_ok :
    tttLargeFiber60Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_9_ok :
    tttLargeFiber60Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_10_ok :
    tttLargeFiber60Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_11_ok :
    tttLargeFiber60Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_12_ok :
    tttLargeFiber60Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_13_ok :
    tttLargeFiber60Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_14_ok :
    tttLargeFiber60Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1Row_15_ok :
    tttLargeFiber60Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_0_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_1_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_2_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_3_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_4_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_5_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_6_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_7_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_8_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_9_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_10_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_11_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_12_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_13_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_14_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentMap_15_ok :
    tttLargeFiber60Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_0_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_1_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_2_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_3_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_4_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_5_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_6_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_7_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_8_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_9_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_10_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_11_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_12_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_13_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_14_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk1ParentPath_15_ok :
    tttLargeFiber60Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber60Block1Chunk1RowCheck 0
    && tttLargeFiber60Block1Chunk1RowCheck 1
    && tttLargeFiber60Block1Chunk1RowCheck 2
    && tttLargeFiber60Block1Chunk1RowCheck 3
    && tttLargeFiber60Block1Chunk1RowCheck 4
    && tttLargeFiber60Block1Chunk1RowCheck 5
    && tttLargeFiber60Block1Chunk1RowCheck 6
    && tttLargeFiber60Block1Chunk1RowCheck 7
    && tttLargeFiber60Block1Chunk1RowCheck 8
    && tttLargeFiber60Block1Chunk1RowCheck 9
    && tttLargeFiber60Block1Chunk1RowCheck 10
    && tttLargeFiber60Block1Chunk1RowCheck 11
    && tttLargeFiber60Block1Chunk1RowCheck 12
    && tttLargeFiber60Block1Chunk1RowCheck 13
    && tttLargeFiber60Block1Chunk1RowCheck 14
    && tttLargeFiber60Block1Chunk1RowCheck 15

theorem tttLargeFiber60Block1Chunk1RowsAudit_ok :
    tttLargeFiber60Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber60Block1Chunk1RowsAudit,
    tttLargeFiber60Block1Chunk1Row_0_ok,
    tttLargeFiber60Block1Chunk1Row_1_ok,
    tttLargeFiber60Block1Chunk1Row_2_ok,
    tttLargeFiber60Block1Chunk1Row_3_ok,
    tttLargeFiber60Block1Chunk1Row_4_ok,
    tttLargeFiber60Block1Chunk1Row_5_ok,
    tttLargeFiber60Block1Chunk1Row_6_ok,
    tttLargeFiber60Block1Chunk1Row_7_ok,
    tttLargeFiber60Block1Chunk1Row_8_ok,
    tttLargeFiber60Block1Chunk1Row_9_ok,
    tttLargeFiber60Block1Chunk1Row_10_ok,
    tttLargeFiber60Block1Chunk1Row_11_ok,
    tttLargeFiber60Block1Chunk1Row_12_ok,
    tttLargeFiber60Block1Chunk1Row_13_ok,
    tttLargeFiber60Block1Chunk1Row_14_ok,
    tttLargeFiber60Block1Chunk1Row_15_ok]

def tttLargeFiber60Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber60Block1Chunk1ParentMapCheck 0
    && tttLargeFiber60Block1Chunk1ParentMapCheck 1
    && tttLargeFiber60Block1Chunk1ParentMapCheck 2
    && tttLargeFiber60Block1Chunk1ParentMapCheck 3
    && tttLargeFiber60Block1Chunk1ParentMapCheck 4
    && tttLargeFiber60Block1Chunk1ParentMapCheck 5
    && tttLargeFiber60Block1Chunk1ParentMapCheck 6
    && tttLargeFiber60Block1Chunk1ParentMapCheck 7
    && tttLargeFiber60Block1Chunk1ParentMapCheck 8
    && tttLargeFiber60Block1Chunk1ParentMapCheck 9
    && tttLargeFiber60Block1Chunk1ParentMapCheck 10
    && tttLargeFiber60Block1Chunk1ParentMapCheck 11
    && tttLargeFiber60Block1Chunk1ParentMapCheck 12
    && tttLargeFiber60Block1Chunk1ParentMapCheck 13
    && tttLargeFiber60Block1Chunk1ParentMapCheck 14
    && tttLargeFiber60Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber60Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber60Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber60Block1Chunk1ParentMapAudit,
    tttLargeFiber60Block1Chunk1ParentMap_0_ok,
    tttLargeFiber60Block1Chunk1ParentMap_1_ok,
    tttLargeFiber60Block1Chunk1ParentMap_2_ok,
    tttLargeFiber60Block1Chunk1ParentMap_3_ok,
    tttLargeFiber60Block1Chunk1ParentMap_4_ok,
    tttLargeFiber60Block1Chunk1ParentMap_5_ok,
    tttLargeFiber60Block1Chunk1ParentMap_6_ok,
    tttLargeFiber60Block1Chunk1ParentMap_7_ok,
    tttLargeFiber60Block1Chunk1ParentMap_8_ok,
    tttLargeFiber60Block1Chunk1ParentMap_9_ok,
    tttLargeFiber60Block1Chunk1ParentMap_10_ok,
    tttLargeFiber60Block1Chunk1ParentMap_11_ok,
    tttLargeFiber60Block1Chunk1ParentMap_12_ok,
    tttLargeFiber60Block1Chunk1ParentMap_13_ok,
    tttLargeFiber60Block1Chunk1ParentMap_14_ok,
    tttLargeFiber60Block1Chunk1ParentMap_15_ok]

def tttLargeFiber60Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber60Block1Chunk1ParentPathCheck 0
    && tttLargeFiber60Block1Chunk1ParentPathCheck 1
    && tttLargeFiber60Block1Chunk1ParentPathCheck 2
    && tttLargeFiber60Block1Chunk1ParentPathCheck 3
    && tttLargeFiber60Block1Chunk1ParentPathCheck 4
    && tttLargeFiber60Block1Chunk1ParentPathCheck 5
    && tttLargeFiber60Block1Chunk1ParentPathCheck 6
    && tttLargeFiber60Block1Chunk1ParentPathCheck 7
    && tttLargeFiber60Block1Chunk1ParentPathCheck 8
    && tttLargeFiber60Block1Chunk1ParentPathCheck 9
    && tttLargeFiber60Block1Chunk1ParentPathCheck 10
    && tttLargeFiber60Block1Chunk1ParentPathCheck 11
    && tttLargeFiber60Block1Chunk1ParentPathCheck 12
    && tttLargeFiber60Block1Chunk1ParentPathCheck 13
    && tttLargeFiber60Block1Chunk1ParentPathCheck 14
    && tttLargeFiber60Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber60Block1Chunk1ParentsAudit_ok :
    tttLargeFiber60Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber60Block1Chunk1ParentsAudit,
    tttLargeFiber60Block1Chunk1ParentPath_0_ok,
    tttLargeFiber60Block1Chunk1ParentPath_1_ok,
    tttLargeFiber60Block1Chunk1ParentPath_2_ok,
    tttLargeFiber60Block1Chunk1ParentPath_3_ok,
    tttLargeFiber60Block1Chunk1ParentPath_4_ok,
    tttLargeFiber60Block1Chunk1ParentPath_5_ok,
    tttLargeFiber60Block1Chunk1ParentPath_6_ok,
    tttLargeFiber60Block1Chunk1ParentPath_7_ok,
    tttLargeFiber60Block1Chunk1ParentPath_8_ok,
    tttLargeFiber60Block1Chunk1ParentPath_9_ok,
    tttLargeFiber60Block1Chunk1ParentPath_10_ok,
    tttLargeFiber60Block1Chunk1ParentPath_11_ok,
    tttLargeFiber60Block1Chunk1ParentPath_12_ok,
    tttLargeFiber60Block1Chunk1ParentPath_13_ok,
    tttLargeFiber60Block1Chunk1ParentPath_14_ok,
    tttLargeFiber60Block1Chunk1ParentPath_15_ok]

def tttLargeFiber60Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block1Chunk1SourcesCheck &&
    tttLargeFiber60Block1Chunk1RowsAudit &&
    tttLargeFiber60Block1Chunk1ParentMapAudit &&
    tttLargeFiber60Block1Chunk1ParentsAudit

theorem tttLargeFiber60Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber60Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block1Chunk1SourcesCheck_ok,
    tttLargeFiber60Block1Chunk1RowsAudit_ok,
    tttLargeFiber60Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber60Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
