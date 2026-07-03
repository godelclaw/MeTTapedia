import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 0 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block0Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block0Chunk2Sources : List Nat :=
  [   576, 577, 578, 579, 580, 581, 582, 583,
   584, 585, 586, 587, 588, 589, 590, 591]

def tttLargeFiber60Row32 : TripleComponentParentRow :=
  tripleRow 576 592 16 100 132 16 102 64
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row33 : TripleComponentParentRow :=
  tripleRow 577 593 16 100 133 16 102 65
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row34 : TripleComponentParentRow :=
  tripleRow 578 566 16 100 134 16 82 34
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row35 : TripleComponentParentRow :=
  tripleRow 579 567 16 100 135 16 82 35
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row36 : TripleComponentParentRow :=
  tripleRow 580 562 16 100 180 16 82 18
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row37 : TripleComponentParentRow :=
  tripleRow 581 583 16 100 181 16 100 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row38 : TripleComponentParentRow :=
  tripleRow 582 561 16 100 182 16 82 17
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber60Row39 : TripleComponentParentRow :=
  tripleRow 583 560 16 100 183 16 82 16
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber60Row40 : TripleComponentParentRow :=
  tripleRow 584 600 16 101 140 16 103 72
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row41 : TripleComponentParentRow :=
  tripleRow 585 601 16 101 141 16 103 73
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row42 : TripleComponentParentRow :=
  tripleRow 586 602 16 101 142 16 103 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
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

def tttLargeFiber60Row43 : TripleComponentParentRow :=
  tripleRow 587 584 16 101 143 16 101 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row44 : TripleComponentParentRow :=
  tripleRow 588 584 16 101 188 16 101 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row45 : TripleComponentParentRow :=
  tripleRow 589 585 16 101 189 16 101 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row46 : TripleComponentParentRow :=
  tripleRow 590 606 16 101 190 16 103 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row47 : TripleComponentParentRow :=
  tripleRow 591 607 16 101 191 16 103 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Block0Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row32
  , tttLargeFiber60Row33
  , tttLargeFiber60Row34
  , tttLargeFiber60Row35
  , tttLargeFiber60Row36
  , tttLargeFiber60Row37
  , tttLargeFiber60Row38
  , tttLargeFiber60Row39
  , tttLargeFiber60Row40
  , tttLargeFiber60Row41
  , tttLargeFiber60Row42
  , tttLargeFiber60Row43
  , tttLargeFiber60Row44
  , tttLargeFiber60Row45
  , tttLargeFiber60Row46
  , tttLargeFiber60Row47
  ]

def tttLargeFiber60Block0Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block0Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block0Chunk2ExpectedContains row.source &&
    tttLargeFiber60Block0Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block0Chunk2SourcesCheck : Bool :=
  (tttLargeFiber60Block0Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber60Block0Chunk2Sources

theorem tttLargeFiber60Block0Chunk2SourcesCheck_ok :
    tttLargeFiber60Block0Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber60Block0Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block0Chunk2RowValid
    (listGetD tttLargeFiber60Block0Chunk2Rows i default)

def tttLargeFiber60Block0Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block0Chunk2Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block0Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block0Chunk2Sources 0 0 == 576
      && tttLargeFiber60ParentOf 576 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block0Chunk2Sources 1 0 == 577
      && tttLargeFiber60ParentOf 577 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block0Chunk2Sources 2 0 == 578
      && tttLargeFiber60ParentOf 578 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block0Chunk2Sources 3 0 == 579
      && tttLargeFiber60ParentOf 579 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block0Chunk2Sources 4 0 == 580
      && tttLargeFiber60ParentOf 580 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block0Chunk2Sources 5 0 == 581
      && tttLargeFiber60ParentOf 581 == 583
      && tttLargeFiber60ParentOf 583 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block0Chunk2Sources 6 0 == 582
      && tttLargeFiber60ParentOf 582 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block0Chunk2Sources 7 0 == 583
      && tttLargeFiber60ParentOf 583 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block0Chunk2Sources 8 0 == 584
      && tttLargeFiber60ParentOf 584 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block0Chunk2Sources 9 0 == 585
      && tttLargeFiber60ParentOf 585 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block0Chunk2Sources 10 0 == 586
      && tttLargeFiber60ParentOf 586 == 602
      && tttLargeFiber60ParentOf 602 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block0Chunk2Sources 11 0 == 587
      && tttLargeFiber60ParentOf 587 == 584
      && tttLargeFiber60ParentOf 584 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block0Chunk2Sources 12 0 == 588
      && tttLargeFiber60ParentOf 588 == 584
      && tttLargeFiber60ParentOf 584 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block0Chunk2Sources 13 0 == 589
      && tttLargeFiber60ParentOf 589 == 585
      && tttLargeFiber60ParentOf 585 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block0Chunk2Sources 14 0 == 590
      && tttLargeFiber60ParentOf 590 == 606
      && tttLargeFiber60ParentOf 606 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block0Chunk2Sources 15 0 == 591
      && tttLargeFiber60ParentOf 591 == 607
      && tttLargeFiber60ParentOf 607 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block0Chunk2Row_0_ok :
    tttLargeFiber60Block0Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_1_ok :
    tttLargeFiber60Block0Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_2_ok :
    tttLargeFiber60Block0Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_3_ok :
    tttLargeFiber60Block0Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_4_ok :
    tttLargeFiber60Block0Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_5_ok :
    tttLargeFiber60Block0Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_6_ok :
    tttLargeFiber60Block0Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_7_ok :
    tttLargeFiber60Block0Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_8_ok :
    tttLargeFiber60Block0Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_9_ok :
    tttLargeFiber60Block0Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_10_ok :
    tttLargeFiber60Block0Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_11_ok :
    tttLargeFiber60Block0Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_12_ok :
    tttLargeFiber60Block0Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_13_ok :
    tttLargeFiber60Block0Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_14_ok :
    tttLargeFiber60Block0Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2Row_15_ok :
    tttLargeFiber60Block0Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_0_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_1_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_2_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_3_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_4_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_5_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_6_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_7_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_8_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_9_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_10_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_11_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_12_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_13_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_14_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentMap_15_ok :
    tttLargeFiber60Block0Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_0_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_1_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_2_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_3_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_4_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_5_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_6_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_7_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_8_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_9_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_10_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_11_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_12_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_13_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_14_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk2ParentPath_15_ok :
    tttLargeFiber60Block0Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block0Chunk2RowsAudit : Bool :=
  tttLargeFiber60Block0Chunk2RowCheck 0
    && tttLargeFiber60Block0Chunk2RowCheck 1
    && tttLargeFiber60Block0Chunk2RowCheck 2
    && tttLargeFiber60Block0Chunk2RowCheck 3
    && tttLargeFiber60Block0Chunk2RowCheck 4
    && tttLargeFiber60Block0Chunk2RowCheck 5
    && tttLargeFiber60Block0Chunk2RowCheck 6
    && tttLargeFiber60Block0Chunk2RowCheck 7
    && tttLargeFiber60Block0Chunk2RowCheck 8
    && tttLargeFiber60Block0Chunk2RowCheck 9
    && tttLargeFiber60Block0Chunk2RowCheck 10
    && tttLargeFiber60Block0Chunk2RowCheck 11
    && tttLargeFiber60Block0Chunk2RowCheck 12
    && tttLargeFiber60Block0Chunk2RowCheck 13
    && tttLargeFiber60Block0Chunk2RowCheck 14
    && tttLargeFiber60Block0Chunk2RowCheck 15

theorem tttLargeFiber60Block0Chunk2RowsAudit_ok :
    tttLargeFiber60Block0Chunk2RowsAudit = true := by
  simp [tttLargeFiber60Block0Chunk2RowsAudit,
    tttLargeFiber60Block0Chunk2Row_0_ok,
    tttLargeFiber60Block0Chunk2Row_1_ok,
    tttLargeFiber60Block0Chunk2Row_2_ok,
    tttLargeFiber60Block0Chunk2Row_3_ok,
    tttLargeFiber60Block0Chunk2Row_4_ok,
    tttLargeFiber60Block0Chunk2Row_5_ok,
    tttLargeFiber60Block0Chunk2Row_6_ok,
    tttLargeFiber60Block0Chunk2Row_7_ok,
    tttLargeFiber60Block0Chunk2Row_8_ok,
    tttLargeFiber60Block0Chunk2Row_9_ok,
    tttLargeFiber60Block0Chunk2Row_10_ok,
    tttLargeFiber60Block0Chunk2Row_11_ok,
    tttLargeFiber60Block0Chunk2Row_12_ok,
    tttLargeFiber60Block0Chunk2Row_13_ok,
    tttLargeFiber60Block0Chunk2Row_14_ok,
    tttLargeFiber60Block0Chunk2Row_15_ok]

def tttLargeFiber60Block0Chunk2ParentMapAudit : Bool :=
  tttLargeFiber60Block0Chunk2ParentMapCheck 0
    && tttLargeFiber60Block0Chunk2ParentMapCheck 1
    && tttLargeFiber60Block0Chunk2ParentMapCheck 2
    && tttLargeFiber60Block0Chunk2ParentMapCheck 3
    && tttLargeFiber60Block0Chunk2ParentMapCheck 4
    && tttLargeFiber60Block0Chunk2ParentMapCheck 5
    && tttLargeFiber60Block0Chunk2ParentMapCheck 6
    && tttLargeFiber60Block0Chunk2ParentMapCheck 7
    && tttLargeFiber60Block0Chunk2ParentMapCheck 8
    && tttLargeFiber60Block0Chunk2ParentMapCheck 9
    && tttLargeFiber60Block0Chunk2ParentMapCheck 10
    && tttLargeFiber60Block0Chunk2ParentMapCheck 11
    && tttLargeFiber60Block0Chunk2ParentMapCheck 12
    && tttLargeFiber60Block0Chunk2ParentMapCheck 13
    && tttLargeFiber60Block0Chunk2ParentMapCheck 14
    && tttLargeFiber60Block0Chunk2ParentMapCheck 15

theorem tttLargeFiber60Block0Chunk2ParentMapAudit_ok :
    tttLargeFiber60Block0Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber60Block0Chunk2ParentMapAudit,
    tttLargeFiber60Block0Chunk2ParentMap_0_ok,
    tttLargeFiber60Block0Chunk2ParentMap_1_ok,
    tttLargeFiber60Block0Chunk2ParentMap_2_ok,
    tttLargeFiber60Block0Chunk2ParentMap_3_ok,
    tttLargeFiber60Block0Chunk2ParentMap_4_ok,
    tttLargeFiber60Block0Chunk2ParentMap_5_ok,
    tttLargeFiber60Block0Chunk2ParentMap_6_ok,
    tttLargeFiber60Block0Chunk2ParentMap_7_ok,
    tttLargeFiber60Block0Chunk2ParentMap_8_ok,
    tttLargeFiber60Block0Chunk2ParentMap_9_ok,
    tttLargeFiber60Block0Chunk2ParentMap_10_ok,
    tttLargeFiber60Block0Chunk2ParentMap_11_ok,
    tttLargeFiber60Block0Chunk2ParentMap_12_ok,
    tttLargeFiber60Block0Chunk2ParentMap_13_ok,
    tttLargeFiber60Block0Chunk2ParentMap_14_ok,
    tttLargeFiber60Block0Chunk2ParentMap_15_ok]

def tttLargeFiber60Block0Chunk2ParentsAudit : Bool :=
  tttLargeFiber60Block0Chunk2ParentPathCheck 0
    && tttLargeFiber60Block0Chunk2ParentPathCheck 1
    && tttLargeFiber60Block0Chunk2ParentPathCheck 2
    && tttLargeFiber60Block0Chunk2ParentPathCheck 3
    && tttLargeFiber60Block0Chunk2ParentPathCheck 4
    && tttLargeFiber60Block0Chunk2ParentPathCheck 5
    && tttLargeFiber60Block0Chunk2ParentPathCheck 6
    && tttLargeFiber60Block0Chunk2ParentPathCheck 7
    && tttLargeFiber60Block0Chunk2ParentPathCheck 8
    && tttLargeFiber60Block0Chunk2ParentPathCheck 9
    && tttLargeFiber60Block0Chunk2ParentPathCheck 10
    && tttLargeFiber60Block0Chunk2ParentPathCheck 11
    && tttLargeFiber60Block0Chunk2ParentPathCheck 12
    && tttLargeFiber60Block0Chunk2ParentPathCheck 13
    && tttLargeFiber60Block0Chunk2ParentPathCheck 14
    && tttLargeFiber60Block0Chunk2ParentPathCheck 15

theorem tttLargeFiber60Block0Chunk2ParentsAudit_ok :
    tttLargeFiber60Block0Chunk2ParentsAudit = true := by
  simp [tttLargeFiber60Block0Chunk2ParentsAudit,
    tttLargeFiber60Block0Chunk2ParentPath_0_ok,
    tttLargeFiber60Block0Chunk2ParentPath_1_ok,
    tttLargeFiber60Block0Chunk2ParentPath_2_ok,
    tttLargeFiber60Block0Chunk2ParentPath_3_ok,
    tttLargeFiber60Block0Chunk2ParentPath_4_ok,
    tttLargeFiber60Block0Chunk2ParentPath_5_ok,
    tttLargeFiber60Block0Chunk2ParentPath_6_ok,
    tttLargeFiber60Block0Chunk2ParentPath_7_ok,
    tttLargeFiber60Block0Chunk2ParentPath_8_ok,
    tttLargeFiber60Block0Chunk2ParentPath_9_ok,
    tttLargeFiber60Block0Chunk2ParentPath_10_ok,
    tttLargeFiber60Block0Chunk2ParentPath_11_ok,
    tttLargeFiber60Block0Chunk2ParentPath_12_ok,
    tttLargeFiber60Block0Chunk2ParentPath_13_ok,
    tttLargeFiber60Block0Chunk2ParentPath_14_ok,
    tttLargeFiber60Block0Chunk2ParentPath_15_ok]

def tttLargeFiber60Block0Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block0Chunk2SourcesCheck &&
    tttLargeFiber60Block0Chunk2RowsAudit &&
    tttLargeFiber60Block0Chunk2ParentMapAudit &&
    tttLargeFiber60Block0Chunk2ParentsAudit

theorem tttLargeFiber60Block0Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber60Block0Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block0Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block0Chunk2SourcesCheck_ok,
    tttLargeFiber60Block0Chunk2RowsAudit_ok,
    tttLargeFiber60Block0Chunk2ParentMapAudit_ok,
    tttLargeFiber60Block0Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block0Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
