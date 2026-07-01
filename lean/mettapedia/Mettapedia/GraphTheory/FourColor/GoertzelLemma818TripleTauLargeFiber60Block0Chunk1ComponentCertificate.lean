import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block0Chunk1Sources : List Nat :=
  [   560, 561, 562, 563, 564, 565, 566, 567,
   568, 569, 570, 571, 572, 573, 574, 575]

def tttLargeFiber60Row16 : TripleComponentParentRow :=
  tripleRow 560 544 16 82 16 16 80 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row17 : TripleComponentParentRow :=
  tripleRow 561 545 16 82 17 16 80 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row18 : TripleComponentParentRow :=
  tripleRow 562 546 16 82 18 16 80 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row19 : TripleComponentParentRow :=
  tripleRow 563 547 16 82 19 16 80 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row20 : TripleComponentParentRow :=
  tripleRow 564 560 16 82 32 16 82 16
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row21 : TripleComponentParentRow :=
  tripleRow 565 561 16 82 33 16 82 17
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row22 : TripleComponentParentRow :=
  tripleRow 566 550 16 82 34 16 80 102
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

def tttLargeFiber60Row23 : TripleComponentParentRow :=
  tripleRow 567 551 16 82 35 16 80 103
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

def tttLargeFiber60Row24 : TripleComponentParentRow :=
  tripleRow 568 552 16 83 24 16 81 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row25 : TripleComponentParentRow :=
  tripleRow 569 553 16 83 25 16 81 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row26 : TripleComponentParentRow :=
  tripleRow 570 554 16 83 26 16 81 90
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row27 : TripleComponentParentRow :=
  tripleRow 571 555 16 83 27 16 81 91
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row28 : TripleComponentParentRow :=
  tripleRow 572 568 16 83 40 16 83 24
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row29 : TripleComponentParentRow :=
  tripleRow 573 569 16 83 41 16 83 25
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row30 : TripleComponentParentRow :=
  tripleRow 574 558 16 83 42 16 81 110
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row31 : TripleComponentParentRow :=
  tripleRow 575 559 16 83 43 16 81 111
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row16
  , tttLargeFiber60Row17
  , tttLargeFiber60Row18
  , tttLargeFiber60Row19
  , tttLargeFiber60Row20
  , tttLargeFiber60Row21
  , tttLargeFiber60Row22
  , tttLargeFiber60Row23
  , tttLargeFiber60Row24
  , tttLargeFiber60Row25
  , tttLargeFiber60Row26
  , tttLargeFiber60Row27
  , tttLargeFiber60Row28
  , tttLargeFiber60Row29
  , tttLargeFiber60Row30
  , tttLargeFiber60Row31
  ]

def tttLargeFiber60Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber60Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber60Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber60Block0Chunk1Sources

theorem tttLargeFiber60Block0Chunk1SourcesCheck_ok :
    tttLargeFiber60Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber60Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block0Chunk1RowValid
    (listGetD tttLargeFiber60Block0Chunk1Rows i default)

def tttLargeFiber60Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block0Chunk1Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block0Chunk1Sources 0 0 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (1 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block0Chunk1Sources 1 0 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block0Chunk1Sources 2 0 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block0Chunk1Sources 3 0 == 563
      && tttLargeFiber60ParentOf 563 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block0Chunk1Sources 4 0 == 564
      && tttLargeFiber60ParentOf 564 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block0Chunk1Sources 5 0 == 565
      && tttLargeFiber60ParentOf 565 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block0Chunk1Sources 6 0 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block0Chunk1Sources 7 0 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block0Chunk1Sources 8 0 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block0Chunk1Sources 9 0 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block0Chunk1Sources 10 0 == 570
      && tttLargeFiber60ParentOf 570 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block0Chunk1Sources 11 0 == 571
      && tttLargeFiber60ParentOf 571 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block0Chunk1Sources 12 0 == 572
      && tttLargeFiber60ParentOf 572 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block0Chunk1Sources 13 0 == 573
      && tttLargeFiber60ParentOf 573 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block0Chunk1Sources 14 0 == 574
      && tttLargeFiber60ParentOf 574 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block0Chunk1Sources 15 0 == 575
      && tttLargeFiber60ParentOf 575 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block0Chunk1Row_0_ok :
    tttLargeFiber60Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_1_ok :
    tttLargeFiber60Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_2_ok :
    tttLargeFiber60Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_3_ok :
    tttLargeFiber60Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_4_ok :
    tttLargeFiber60Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_5_ok :
    tttLargeFiber60Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_6_ok :
    tttLargeFiber60Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_7_ok :
    tttLargeFiber60Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_8_ok :
    tttLargeFiber60Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_9_ok :
    tttLargeFiber60Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_10_ok :
    tttLargeFiber60Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_11_ok :
    tttLargeFiber60Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_12_ok :
    tttLargeFiber60Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_13_ok :
    tttLargeFiber60Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_14_ok :
    tttLargeFiber60Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1Row_15_ok :
    tttLargeFiber60Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_0_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_1_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_2_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_3_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_4_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_5_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_6_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_7_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_8_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_9_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_10_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_11_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_12_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_13_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_14_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentMap_15_ok :
    tttLargeFiber60Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_0_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_1_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_2_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_3_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_4_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_5_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_6_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_7_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_8_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_9_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_10_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_11_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_12_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_13_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_14_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk1ParentPath_15_ok :
    tttLargeFiber60Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber60Block0Chunk1RowCheck 0
    && tttLargeFiber60Block0Chunk1RowCheck 1
    && tttLargeFiber60Block0Chunk1RowCheck 2
    && tttLargeFiber60Block0Chunk1RowCheck 3
    && tttLargeFiber60Block0Chunk1RowCheck 4
    && tttLargeFiber60Block0Chunk1RowCheck 5
    && tttLargeFiber60Block0Chunk1RowCheck 6
    && tttLargeFiber60Block0Chunk1RowCheck 7
    && tttLargeFiber60Block0Chunk1RowCheck 8
    && tttLargeFiber60Block0Chunk1RowCheck 9
    && tttLargeFiber60Block0Chunk1RowCheck 10
    && tttLargeFiber60Block0Chunk1RowCheck 11
    && tttLargeFiber60Block0Chunk1RowCheck 12
    && tttLargeFiber60Block0Chunk1RowCheck 13
    && tttLargeFiber60Block0Chunk1RowCheck 14
    && tttLargeFiber60Block0Chunk1RowCheck 15

theorem tttLargeFiber60Block0Chunk1RowsAudit_ok :
    tttLargeFiber60Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber60Block0Chunk1RowsAudit,
    tttLargeFiber60Block0Chunk1Row_0_ok,
    tttLargeFiber60Block0Chunk1Row_1_ok,
    tttLargeFiber60Block0Chunk1Row_2_ok,
    tttLargeFiber60Block0Chunk1Row_3_ok,
    tttLargeFiber60Block0Chunk1Row_4_ok,
    tttLargeFiber60Block0Chunk1Row_5_ok,
    tttLargeFiber60Block0Chunk1Row_6_ok,
    tttLargeFiber60Block0Chunk1Row_7_ok,
    tttLargeFiber60Block0Chunk1Row_8_ok,
    tttLargeFiber60Block0Chunk1Row_9_ok,
    tttLargeFiber60Block0Chunk1Row_10_ok,
    tttLargeFiber60Block0Chunk1Row_11_ok,
    tttLargeFiber60Block0Chunk1Row_12_ok,
    tttLargeFiber60Block0Chunk1Row_13_ok,
    tttLargeFiber60Block0Chunk1Row_14_ok,
    tttLargeFiber60Block0Chunk1Row_15_ok]

def tttLargeFiber60Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber60Block0Chunk1ParentMapCheck 0
    && tttLargeFiber60Block0Chunk1ParentMapCheck 1
    && tttLargeFiber60Block0Chunk1ParentMapCheck 2
    && tttLargeFiber60Block0Chunk1ParentMapCheck 3
    && tttLargeFiber60Block0Chunk1ParentMapCheck 4
    && tttLargeFiber60Block0Chunk1ParentMapCheck 5
    && tttLargeFiber60Block0Chunk1ParentMapCheck 6
    && tttLargeFiber60Block0Chunk1ParentMapCheck 7
    && tttLargeFiber60Block0Chunk1ParentMapCheck 8
    && tttLargeFiber60Block0Chunk1ParentMapCheck 9
    && tttLargeFiber60Block0Chunk1ParentMapCheck 10
    && tttLargeFiber60Block0Chunk1ParentMapCheck 11
    && tttLargeFiber60Block0Chunk1ParentMapCheck 12
    && tttLargeFiber60Block0Chunk1ParentMapCheck 13
    && tttLargeFiber60Block0Chunk1ParentMapCheck 14
    && tttLargeFiber60Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber60Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber60Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber60Block0Chunk1ParentMapAudit,
    tttLargeFiber60Block0Chunk1ParentMap_0_ok,
    tttLargeFiber60Block0Chunk1ParentMap_1_ok,
    tttLargeFiber60Block0Chunk1ParentMap_2_ok,
    tttLargeFiber60Block0Chunk1ParentMap_3_ok,
    tttLargeFiber60Block0Chunk1ParentMap_4_ok,
    tttLargeFiber60Block0Chunk1ParentMap_5_ok,
    tttLargeFiber60Block0Chunk1ParentMap_6_ok,
    tttLargeFiber60Block0Chunk1ParentMap_7_ok,
    tttLargeFiber60Block0Chunk1ParentMap_8_ok,
    tttLargeFiber60Block0Chunk1ParentMap_9_ok,
    tttLargeFiber60Block0Chunk1ParentMap_10_ok,
    tttLargeFiber60Block0Chunk1ParentMap_11_ok,
    tttLargeFiber60Block0Chunk1ParentMap_12_ok,
    tttLargeFiber60Block0Chunk1ParentMap_13_ok,
    tttLargeFiber60Block0Chunk1ParentMap_14_ok,
    tttLargeFiber60Block0Chunk1ParentMap_15_ok]

def tttLargeFiber60Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber60Block0Chunk1ParentPathCheck 0
    && tttLargeFiber60Block0Chunk1ParentPathCheck 1
    && tttLargeFiber60Block0Chunk1ParentPathCheck 2
    && tttLargeFiber60Block0Chunk1ParentPathCheck 3
    && tttLargeFiber60Block0Chunk1ParentPathCheck 4
    && tttLargeFiber60Block0Chunk1ParentPathCheck 5
    && tttLargeFiber60Block0Chunk1ParentPathCheck 6
    && tttLargeFiber60Block0Chunk1ParentPathCheck 7
    && tttLargeFiber60Block0Chunk1ParentPathCheck 8
    && tttLargeFiber60Block0Chunk1ParentPathCheck 9
    && tttLargeFiber60Block0Chunk1ParentPathCheck 10
    && tttLargeFiber60Block0Chunk1ParentPathCheck 11
    && tttLargeFiber60Block0Chunk1ParentPathCheck 12
    && tttLargeFiber60Block0Chunk1ParentPathCheck 13
    && tttLargeFiber60Block0Chunk1ParentPathCheck 14
    && tttLargeFiber60Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber60Block0Chunk1ParentsAudit_ok :
    tttLargeFiber60Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber60Block0Chunk1ParentsAudit,
    tttLargeFiber60Block0Chunk1ParentPath_0_ok,
    tttLargeFiber60Block0Chunk1ParentPath_1_ok,
    tttLargeFiber60Block0Chunk1ParentPath_2_ok,
    tttLargeFiber60Block0Chunk1ParentPath_3_ok,
    tttLargeFiber60Block0Chunk1ParentPath_4_ok,
    tttLargeFiber60Block0Chunk1ParentPath_5_ok,
    tttLargeFiber60Block0Chunk1ParentPath_6_ok,
    tttLargeFiber60Block0Chunk1ParentPath_7_ok,
    tttLargeFiber60Block0Chunk1ParentPath_8_ok,
    tttLargeFiber60Block0Chunk1ParentPath_9_ok,
    tttLargeFiber60Block0Chunk1ParentPath_10_ok,
    tttLargeFiber60Block0Chunk1ParentPath_11_ok,
    tttLargeFiber60Block0Chunk1ParentPath_12_ok,
    tttLargeFiber60Block0Chunk1ParentPath_13_ok,
    tttLargeFiber60Block0Chunk1ParentPath_14_ok,
    tttLargeFiber60Block0Chunk1ParentPath_15_ok]

def tttLargeFiber60Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block0Chunk1SourcesCheck &&
    tttLargeFiber60Block0Chunk1RowsAudit &&
    tttLargeFiber60Block0Chunk1ParentMapAudit &&
    tttLargeFiber60Block0Chunk1ParentsAudit

theorem tttLargeFiber60Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber60Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block0Chunk1SourcesCheck_ok,
    tttLargeFiber60Block0Chunk1RowsAudit_ok,
    tttLargeFiber60Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber60Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
