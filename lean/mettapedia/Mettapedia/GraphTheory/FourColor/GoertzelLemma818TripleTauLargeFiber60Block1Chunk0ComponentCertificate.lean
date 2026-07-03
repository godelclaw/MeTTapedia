import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block1Chunk0Sources : List Nat :=
  [   608, 609, 610, 611, 612, 613, 614, 615,
   616, 617, 618, 619, 620, 621, 622, 623]

def tttLargeFiber60Row64 : TripleComponentParentRow :=
  tripleRow 608 544 17 88 80 16 80 80
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row65 : TripleComponentParentRow :=
  tripleRow 609 545 17 88 81 16 80 81
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row66 : TripleComponentParentRow :=
  tripleRow 610 546 17 88 82 16 80 82
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row67 : TripleComponentParentRow :=
  tripleRow 611 547 17 88 83 16 80 83
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row68 : TripleComponentParentRow :=
  tripleRow 612 548 17 88 100 16 80 100
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row69 : TripleComponentParentRow :=
  tripleRow 613 549 17 88 101 16 80 101
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row70 : TripleComponentParentRow :=
  tripleRow 614 550 17 88 102 16 80 102
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row71 : TripleComponentParentRow :=
  tripleRow 615 551 17 88 103 16 80 103
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row72 : TripleComponentParentRow :=
  tripleRow 616 552 17 89 88 16 81 88
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row73 : TripleComponentParentRow :=
  tripleRow 617 553 17 89 89 16 81 89
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row74 : TripleComponentParentRow :=
  tripleRow 618 554 17 89 90 16 81 90
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row75 : TripleComponentParentRow :=
  tripleRow 619 555 17 89 91 16 81 91
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row76 : TripleComponentParentRow :=
  tripleRow 620 556 17 89 108 16 81 108
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row77 : TripleComponentParentRow :=
  tripleRow 621 557 17 89 109 16 81 109
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row78 : TripleComponentParentRow :=
  tripleRow 622 558 17 89 110 16 81 110
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row79 : TripleComponentParentRow :=
  tripleRow 623 559 17 89 111 16 81 111
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row64
  , tttLargeFiber60Row65
  , tttLargeFiber60Row66
  , tttLargeFiber60Row67
  , tttLargeFiber60Row68
  , tttLargeFiber60Row69
  , tttLargeFiber60Row70
  , tttLargeFiber60Row71
  , tttLargeFiber60Row72
  , tttLargeFiber60Row73
  , tttLargeFiber60Row74
  , tttLargeFiber60Row75
  , tttLargeFiber60Row76
  , tttLargeFiber60Row77
  , tttLargeFiber60Row78
  , tttLargeFiber60Row79
  ]

def tttLargeFiber60Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber60Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber60Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber60Block1Chunk0Sources

theorem tttLargeFiber60Block1Chunk0SourcesCheck_ok :
    tttLargeFiber60Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber60Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block1Chunk0RowValid
    (listGetD tttLargeFiber60Block1Chunk0Rows i default)

def tttLargeFiber60Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block1Chunk0Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block1Chunk0Sources 0 0 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (1 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block1Chunk0Sources 1 0 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block1Chunk0Sources 2 0 == 610
      && tttLargeFiber60ParentOf 610 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block1Chunk0Sources 3 0 == 611
      && tttLargeFiber60ParentOf 611 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block1Chunk0Sources 4 0 == 612
      && tttLargeFiber60ParentOf 612 == 548
      && tttLargeFiber60ParentOf 548 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block1Chunk0Sources 5 0 == 613
      && tttLargeFiber60ParentOf 613 == 549
      && tttLargeFiber60ParentOf 549 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block1Chunk0Sources 6 0 == 614
      && tttLargeFiber60ParentOf 614 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block1Chunk0Sources 7 0 == 615
      && tttLargeFiber60ParentOf 615 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block1Chunk0Sources 8 0 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block1Chunk0Sources 9 0 == 617
      && tttLargeFiber60ParentOf 617 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block1Chunk0Sources 10 0 == 618
      && tttLargeFiber60ParentOf 618 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block1Chunk0Sources 11 0 == 619
      && tttLargeFiber60ParentOf 619 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block1Chunk0Sources 12 0 == 620
      && tttLargeFiber60ParentOf 620 == 556
      && tttLargeFiber60ParentOf 556 == 548
      && tttLargeFiber60ParentOf 548 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block1Chunk0Sources 13 0 == 621
      && tttLargeFiber60ParentOf 621 == 557
      && tttLargeFiber60ParentOf 557 == 549
      && tttLargeFiber60ParentOf 549 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block1Chunk0Sources 14 0 == 622
      && tttLargeFiber60ParentOf 622 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block1Chunk0Sources 15 0 == 623
      && tttLargeFiber60ParentOf 623 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block1Chunk0Row_0_ok :
    tttLargeFiber60Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_1_ok :
    tttLargeFiber60Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_2_ok :
    tttLargeFiber60Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_3_ok :
    tttLargeFiber60Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_4_ok :
    tttLargeFiber60Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_5_ok :
    tttLargeFiber60Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_6_ok :
    tttLargeFiber60Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_7_ok :
    tttLargeFiber60Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_8_ok :
    tttLargeFiber60Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_9_ok :
    tttLargeFiber60Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_10_ok :
    tttLargeFiber60Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_11_ok :
    tttLargeFiber60Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_12_ok :
    tttLargeFiber60Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_13_ok :
    tttLargeFiber60Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_14_ok :
    tttLargeFiber60Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0Row_15_ok :
    tttLargeFiber60Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_0_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_1_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_2_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_3_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_4_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_5_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_6_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_7_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_8_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_9_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_10_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_11_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_12_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_13_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_14_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentMap_15_ok :
    tttLargeFiber60Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_0_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_1_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_2_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_3_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_4_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_5_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_6_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_7_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_8_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_9_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_10_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_11_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_12_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_13_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_14_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk0ParentPath_15_ok :
    tttLargeFiber60Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber60Block1Chunk0RowCheck 0
    && tttLargeFiber60Block1Chunk0RowCheck 1
    && tttLargeFiber60Block1Chunk0RowCheck 2
    && tttLargeFiber60Block1Chunk0RowCheck 3
    && tttLargeFiber60Block1Chunk0RowCheck 4
    && tttLargeFiber60Block1Chunk0RowCheck 5
    && tttLargeFiber60Block1Chunk0RowCheck 6
    && tttLargeFiber60Block1Chunk0RowCheck 7
    && tttLargeFiber60Block1Chunk0RowCheck 8
    && tttLargeFiber60Block1Chunk0RowCheck 9
    && tttLargeFiber60Block1Chunk0RowCheck 10
    && tttLargeFiber60Block1Chunk0RowCheck 11
    && tttLargeFiber60Block1Chunk0RowCheck 12
    && tttLargeFiber60Block1Chunk0RowCheck 13
    && tttLargeFiber60Block1Chunk0RowCheck 14
    && tttLargeFiber60Block1Chunk0RowCheck 15

theorem tttLargeFiber60Block1Chunk0RowsAudit_ok :
    tttLargeFiber60Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber60Block1Chunk0RowsAudit,
    tttLargeFiber60Block1Chunk0Row_0_ok,
    tttLargeFiber60Block1Chunk0Row_1_ok,
    tttLargeFiber60Block1Chunk0Row_2_ok,
    tttLargeFiber60Block1Chunk0Row_3_ok,
    tttLargeFiber60Block1Chunk0Row_4_ok,
    tttLargeFiber60Block1Chunk0Row_5_ok,
    tttLargeFiber60Block1Chunk0Row_6_ok,
    tttLargeFiber60Block1Chunk0Row_7_ok,
    tttLargeFiber60Block1Chunk0Row_8_ok,
    tttLargeFiber60Block1Chunk0Row_9_ok,
    tttLargeFiber60Block1Chunk0Row_10_ok,
    tttLargeFiber60Block1Chunk0Row_11_ok,
    tttLargeFiber60Block1Chunk0Row_12_ok,
    tttLargeFiber60Block1Chunk0Row_13_ok,
    tttLargeFiber60Block1Chunk0Row_14_ok,
    tttLargeFiber60Block1Chunk0Row_15_ok]

def tttLargeFiber60Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber60Block1Chunk0ParentMapCheck 0
    && tttLargeFiber60Block1Chunk0ParentMapCheck 1
    && tttLargeFiber60Block1Chunk0ParentMapCheck 2
    && tttLargeFiber60Block1Chunk0ParentMapCheck 3
    && tttLargeFiber60Block1Chunk0ParentMapCheck 4
    && tttLargeFiber60Block1Chunk0ParentMapCheck 5
    && tttLargeFiber60Block1Chunk0ParentMapCheck 6
    && tttLargeFiber60Block1Chunk0ParentMapCheck 7
    && tttLargeFiber60Block1Chunk0ParentMapCheck 8
    && tttLargeFiber60Block1Chunk0ParentMapCheck 9
    && tttLargeFiber60Block1Chunk0ParentMapCheck 10
    && tttLargeFiber60Block1Chunk0ParentMapCheck 11
    && tttLargeFiber60Block1Chunk0ParentMapCheck 12
    && tttLargeFiber60Block1Chunk0ParentMapCheck 13
    && tttLargeFiber60Block1Chunk0ParentMapCheck 14
    && tttLargeFiber60Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber60Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber60Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber60Block1Chunk0ParentMapAudit,
    tttLargeFiber60Block1Chunk0ParentMap_0_ok,
    tttLargeFiber60Block1Chunk0ParentMap_1_ok,
    tttLargeFiber60Block1Chunk0ParentMap_2_ok,
    tttLargeFiber60Block1Chunk0ParentMap_3_ok,
    tttLargeFiber60Block1Chunk0ParentMap_4_ok,
    tttLargeFiber60Block1Chunk0ParentMap_5_ok,
    tttLargeFiber60Block1Chunk0ParentMap_6_ok,
    tttLargeFiber60Block1Chunk0ParentMap_7_ok,
    tttLargeFiber60Block1Chunk0ParentMap_8_ok,
    tttLargeFiber60Block1Chunk0ParentMap_9_ok,
    tttLargeFiber60Block1Chunk0ParentMap_10_ok,
    tttLargeFiber60Block1Chunk0ParentMap_11_ok,
    tttLargeFiber60Block1Chunk0ParentMap_12_ok,
    tttLargeFiber60Block1Chunk0ParentMap_13_ok,
    tttLargeFiber60Block1Chunk0ParentMap_14_ok,
    tttLargeFiber60Block1Chunk0ParentMap_15_ok]

def tttLargeFiber60Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber60Block1Chunk0ParentPathCheck 0
    && tttLargeFiber60Block1Chunk0ParentPathCheck 1
    && tttLargeFiber60Block1Chunk0ParentPathCheck 2
    && tttLargeFiber60Block1Chunk0ParentPathCheck 3
    && tttLargeFiber60Block1Chunk0ParentPathCheck 4
    && tttLargeFiber60Block1Chunk0ParentPathCheck 5
    && tttLargeFiber60Block1Chunk0ParentPathCheck 6
    && tttLargeFiber60Block1Chunk0ParentPathCheck 7
    && tttLargeFiber60Block1Chunk0ParentPathCheck 8
    && tttLargeFiber60Block1Chunk0ParentPathCheck 9
    && tttLargeFiber60Block1Chunk0ParentPathCheck 10
    && tttLargeFiber60Block1Chunk0ParentPathCheck 11
    && tttLargeFiber60Block1Chunk0ParentPathCheck 12
    && tttLargeFiber60Block1Chunk0ParentPathCheck 13
    && tttLargeFiber60Block1Chunk0ParentPathCheck 14
    && tttLargeFiber60Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber60Block1Chunk0ParentsAudit_ok :
    tttLargeFiber60Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber60Block1Chunk0ParentsAudit,
    tttLargeFiber60Block1Chunk0ParentPath_0_ok,
    tttLargeFiber60Block1Chunk0ParentPath_1_ok,
    tttLargeFiber60Block1Chunk0ParentPath_2_ok,
    tttLargeFiber60Block1Chunk0ParentPath_3_ok,
    tttLargeFiber60Block1Chunk0ParentPath_4_ok,
    tttLargeFiber60Block1Chunk0ParentPath_5_ok,
    tttLargeFiber60Block1Chunk0ParentPath_6_ok,
    tttLargeFiber60Block1Chunk0ParentPath_7_ok,
    tttLargeFiber60Block1Chunk0ParentPath_8_ok,
    tttLargeFiber60Block1Chunk0ParentPath_9_ok,
    tttLargeFiber60Block1Chunk0ParentPath_10_ok,
    tttLargeFiber60Block1Chunk0ParentPath_11_ok,
    tttLargeFiber60Block1Chunk0ParentPath_12_ok,
    tttLargeFiber60Block1Chunk0ParentPath_13_ok,
    tttLargeFiber60Block1Chunk0ParentPath_14_ok,
    tttLargeFiber60Block1Chunk0ParentPath_15_ok]

def tttLargeFiber60Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block1Chunk0SourcesCheck &&
    tttLargeFiber60Block1Chunk0RowsAudit &&
    tttLargeFiber60Block1Chunk0ParentMapAudit &&
    tttLargeFiber60Block1Chunk0ParentsAudit

theorem tttLargeFiber60Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber60Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block1Chunk0SourcesCheck_ok,
    tttLargeFiber60Block1Chunk0RowsAudit_ok,
    tttLargeFiber60Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber60Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
