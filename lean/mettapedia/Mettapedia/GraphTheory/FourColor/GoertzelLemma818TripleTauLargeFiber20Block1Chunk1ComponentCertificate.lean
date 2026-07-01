import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block1Chunk1Sources : List Nat :=
  [   4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727,
   4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735]

def tttLargeFiber20Row80 : TripleComponentParentRow :=
  tripleRow 4720 4656 141 158 0 140 150 0
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row81 : TripleComponentParentRow :=
  tripleRow 4721 4657 141 158 1 140 150 1
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row82 : TripleComponentParentRow :=
  tripleRow 4722 4658 141 158 2 140 150 2
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row83 : TripleComponentParentRow :=
  tripleRow 4723 4659 141 158 3 140 150 3
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row84 : TripleComponentParentRow :=
  tripleRow 4724 4660 141 158 48 140 150 48
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row85 : TripleComponentParentRow :=
  tripleRow 4725 4661 141 158 49 140 150 49
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row86 : TripleComponentParentRow :=
  tripleRow 4726 4662 141 158 50 140 150 50
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row87 : TripleComponentParentRow :=
  tripleRow 4727 4663 141 158 51 140 150 51
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row88 : TripleComponentParentRow :=
  tripleRow 4728 4664 141 159 8 140 151 8
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row89 : TripleComponentParentRow :=
  tripleRow 4729 4665 141 159 9 140 151 9
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row90 : TripleComponentParentRow :=
  tripleRow 4730 4666 141 159 10 140 151 10
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row91 : TripleComponentParentRow :=
  tripleRow 4731 4667 141 159 11 140 151 11
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row92 : TripleComponentParentRow :=
  tripleRow 4732 4668 141 159 56 140 151 56
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row93 : TripleComponentParentRow :=
  tripleRow 4733 4669 141 159 57 140 151 57
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row94 : TripleComponentParentRow :=
  tripleRow 4734 4670 141 159 58 140 151 58
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row95 : TripleComponentParentRow :=
  tripleRow 4735 4671 141 159 59 140 151 59
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row80
  , tttLargeFiber20Row81
  , tttLargeFiber20Row82
  , tttLargeFiber20Row83
  , tttLargeFiber20Row84
  , tttLargeFiber20Row85
  , tttLargeFiber20Row86
  , tttLargeFiber20Row87
  , tttLargeFiber20Row88
  , tttLargeFiber20Row89
  , tttLargeFiber20Row90
  , tttLargeFiber20Row91
  , tttLargeFiber20Row92
  , tttLargeFiber20Row93
  , tttLargeFiber20Row94
  , tttLargeFiber20Row95
  ]

def tttLargeFiber20Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber20Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber20Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber20Block1Chunk1Sources

theorem tttLargeFiber20Block1Chunk1SourcesCheck_ok :
    tttLargeFiber20Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber20Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block1Chunk1RowValid
    (listGetD tttLargeFiber20Block1Chunk1Rows i default)

def tttLargeFiber20Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block1Chunk1Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block1Chunk1Sources 0 0 == 4720
      && tttLargeFiber20ParentOf 4720 == 4656
      && tttLargeFiber20ParentOf 4656 == 4660
      && tttLargeFiber20ParentOf 4660 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block1Chunk1Sources 1 0 == 4721
      && tttLargeFiber20ParentOf 4721 == 4657
      && tttLargeFiber20ParentOf 4657 == 4661
      && tttLargeFiber20ParentOf 4661 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block1Chunk1Sources 2 0 == 4722
      && tttLargeFiber20ParentOf 4722 == 4658
      && tttLargeFiber20ParentOf 4658 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block1Chunk1Sources 3 0 == 4723
      && tttLargeFiber20ParentOf 4723 == 4659
      && tttLargeFiber20ParentOf 4659 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block1Chunk1Sources 4 0 == 4724
      && tttLargeFiber20ParentOf 4724 == 4660
      && tttLargeFiber20ParentOf 4660 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block1Chunk1Sources 5 0 == 4725
      && tttLargeFiber20ParentOf 4725 == 4661
      && tttLargeFiber20ParentOf 4661 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block1Chunk1Sources 6 0 == 4726
      && tttLargeFiber20ParentOf 4726 == 4662
      && tttLargeFiber20ParentOf 4662 == 4650
      && tttLargeFiber20ParentOf 4650 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block1Chunk1Sources 7 0 == 4727
      && tttLargeFiber20ParentOf 4727 == 4663
      && tttLargeFiber20ParentOf 4663 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block1Chunk1Sources 8 0 == 4728
      && tttLargeFiber20ParentOf 4728 == 4664
      && tttLargeFiber20ParentOf 4664 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block1Chunk1Sources 9 0 == 4729
      && tttLargeFiber20ParentOf 4729 == 4665
      && tttLargeFiber20ParentOf 4665 == 4669
      && tttLargeFiber20ParentOf 4669 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block1Chunk1Sources 10 0 == 4730
      && tttLargeFiber20ParentOf 4730 == 4666
      && tttLargeFiber20ParentOf 4666 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block1Chunk1Sources 11 0 == 4731
      && tttLargeFiber20ParentOf 4731 == 4667
      && tttLargeFiber20ParentOf 4667 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block1Chunk1Sources 12 0 == 4732
      && tttLargeFiber20ParentOf 4732 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block1Chunk1Sources 13 0 == 4733
      && tttLargeFiber20ParentOf 4733 == 4669
      && tttLargeFiber20ParentOf 4669 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block1Chunk1Sources 14 0 == 4734
      && tttLargeFiber20ParentOf 4734 == 4670
      && tttLargeFiber20ParentOf 4670 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block1Chunk1Sources 15 0 == 4735
      && tttLargeFiber20ParentOf 4735 == 4671
      && tttLargeFiber20ParentOf 4671 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block1Chunk1Row_0_ok :
    tttLargeFiber20Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_1_ok :
    tttLargeFiber20Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_2_ok :
    tttLargeFiber20Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_3_ok :
    tttLargeFiber20Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_4_ok :
    tttLargeFiber20Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_5_ok :
    tttLargeFiber20Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_6_ok :
    tttLargeFiber20Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_7_ok :
    tttLargeFiber20Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_8_ok :
    tttLargeFiber20Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_9_ok :
    tttLargeFiber20Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_10_ok :
    tttLargeFiber20Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_11_ok :
    tttLargeFiber20Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_12_ok :
    tttLargeFiber20Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_13_ok :
    tttLargeFiber20Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_14_ok :
    tttLargeFiber20Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1Row_15_ok :
    tttLargeFiber20Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_0_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_1_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_2_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_3_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_4_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_5_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_6_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_7_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_8_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_9_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_10_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_11_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_12_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_13_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_14_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentMap_15_ok :
    tttLargeFiber20Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_0_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_1_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_2_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_3_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_4_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_5_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_6_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_7_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_8_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_9_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_10_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_11_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_12_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_13_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_14_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk1ParentPath_15_ok :
    tttLargeFiber20Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber20Block1Chunk1RowCheck 0
    && tttLargeFiber20Block1Chunk1RowCheck 1
    && tttLargeFiber20Block1Chunk1RowCheck 2
    && tttLargeFiber20Block1Chunk1RowCheck 3
    && tttLargeFiber20Block1Chunk1RowCheck 4
    && tttLargeFiber20Block1Chunk1RowCheck 5
    && tttLargeFiber20Block1Chunk1RowCheck 6
    && tttLargeFiber20Block1Chunk1RowCheck 7
    && tttLargeFiber20Block1Chunk1RowCheck 8
    && tttLargeFiber20Block1Chunk1RowCheck 9
    && tttLargeFiber20Block1Chunk1RowCheck 10
    && tttLargeFiber20Block1Chunk1RowCheck 11
    && tttLargeFiber20Block1Chunk1RowCheck 12
    && tttLargeFiber20Block1Chunk1RowCheck 13
    && tttLargeFiber20Block1Chunk1RowCheck 14
    && tttLargeFiber20Block1Chunk1RowCheck 15

theorem tttLargeFiber20Block1Chunk1RowsAudit_ok :
    tttLargeFiber20Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber20Block1Chunk1RowsAudit,
    tttLargeFiber20Block1Chunk1Row_0_ok,
    tttLargeFiber20Block1Chunk1Row_1_ok,
    tttLargeFiber20Block1Chunk1Row_2_ok,
    tttLargeFiber20Block1Chunk1Row_3_ok,
    tttLargeFiber20Block1Chunk1Row_4_ok,
    tttLargeFiber20Block1Chunk1Row_5_ok,
    tttLargeFiber20Block1Chunk1Row_6_ok,
    tttLargeFiber20Block1Chunk1Row_7_ok,
    tttLargeFiber20Block1Chunk1Row_8_ok,
    tttLargeFiber20Block1Chunk1Row_9_ok,
    tttLargeFiber20Block1Chunk1Row_10_ok,
    tttLargeFiber20Block1Chunk1Row_11_ok,
    tttLargeFiber20Block1Chunk1Row_12_ok,
    tttLargeFiber20Block1Chunk1Row_13_ok,
    tttLargeFiber20Block1Chunk1Row_14_ok,
    tttLargeFiber20Block1Chunk1Row_15_ok]

def tttLargeFiber20Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber20Block1Chunk1ParentMapCheck 0
    && tttLargeFiber20Block1Chunk1ParentMapCheck 1
    && tttLargeFiber20Block1Chunk1ParentMapCheck 2
    && tttLargeFiber20Block1Chunk1ParentMapCheck 3
    && tttLargeFiber20Block1Chunk1ParentMapCheck 4
    && tttLargeFiber20Block1Chunk1ParentMapCheck 5
    && tttLargeFiber20Block1Chunk1ParentMapCheck 6
    && tttLargeFiber20Block1Chunk1ParentMapCheck 7
    && tttLargeFiber20Block1Chunk1ParentMapCheck 8
    && tttLargeFiber20Block1Chunk1ParentMapCheck 9
    && tttLargeFiber20Block1Chunk1ParentMapCheck 10
    && tttLargeFiber20Block1Chunk1ParentMapCheck 11
    && tttLargeFiber20Block1Chunk1ParentMapCheck 12
    && tttLargeFiber20Block1Chunk1ParentMapCheck 13
    && tttLargeFiber20Block1Chunk1ParentMapCheck 14
    && tttLargeFiber20Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber20Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber20Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber20Block1Chunk1ParentMapAudit,
    tttLargeFiber20Block1Chunk1ParentMap_0_ok,
    tttLargeFiber20Block1Chunk1ParentMap_1_ok,
    tttLargeFiber20Block1Chunk1ParentMap_2_ok,
    tttLargeFiber20Block1Chunk1ParentMap_3_ok,
    tttLargeFiber20Block1Chunk1ParentMap_4_ok,
    tttLargeFiber20Block1Chunk1ParentMap_5_ok,
    tttLargeFiber20Block1Chunk1ParentMap_6_ok,
    tttLargeFiber20Block1Chunk1ParentMap_7_ok,
    tttLargeFiber20Block1Chunk1ParentMap_8_ok,
    tttLargeFiber20Block1Chunk1ParentMap_9_ok,
    tttLargeFiber20Block1Chunk1ParentMap_10_ok,
    tttLargeFiber20Block1Chunk1ParentMap_11_ok,
    tttLargeFiber20Block1Chunk1ParentMap_12_ok,
    tttLargeFiber20Block1Chunk1ParentMap_13_ok,
    tttLargeFiber20Block1Chunk1ParentMap_14_ok,
    tttLargeFiber20Block1Chunk1ParentMap_15_ok]

def tttLargeFiber20Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber20Block1Chunk1ParentPathCheck 0
    && tttLargeFiber20Block1Chunk1ParentPathCheck 1
    && tttLargeFiber20Block1Chunk1ParentPathCheck 2
    && tttLargeFiber20Block1Chunk1ParentPathCheck 3
    && tttLargeFiber20Block1Chunk1ParentPathCheck 4
    && tttLargeFiber20Block1Chunk1ParentPathCheck 5
    && tttLargeFiber20Block1Chunk1ParentPathCheck 6
    && tttLargeFiber20Block1Chunk1ParentPathCheck 7
    && tttLargeFiber20Block1Chunk1ParentPathCheck 8
    && tttLargeFiber20Block1Chunk1ParentPathCheck 9
    && tttLargeFiber20Block1Chunk1ParentPathCheck 10
    && tttLargeFiber20Block1Chunk1ParentPathCheck 11
    && tttLargeFiber20Block1Chunk1ParentPathCheck 12
    && tttLargeFiber20Block1Chunk1ParentPathCheck 13
    && tttLargeFiber20Block1Chunk1ParentPathCheck 14
    && tttLargeFiber20Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber20Block1Chunk1ParentsAudit_ok :
    tttLargeFiber20Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber20Block1Chunk1ParentsAudit,
    tttLargeFiber20Block1Chunk1ParentPath_0_ok,
    tttLargeFiber20Block1Chunk1ParentPath_1_ok,
    tttLargeFiber20Block1Chunk1ParentPath_2_ok,
    tttLargeFiber20Block1Chunk1ParentPath_3_ok,
    tttLargeFiber20Block1Chunk1ParentPath_4_ok,
    tttLargeFiber20Block1Chunk1ParentPath_5_ok,
    tttLargeFiber20Block1Chunk1ParentPath_6_ok,
    tttLargeFiber20Block1Chunk1ParentPath_7_ok,
    tttLargeFiber20Block1Chunk1ParentPath_8_ok,
    tttLargeFiber20Block1Chunk1ParentPath_9_ok,
    tttLargeFiber20Block1Chunk1ParentPath_10_ok,
    tttLargeFiber20Block1Chunk1ParentPath_11_ok,
    tttLargeFiber20Block1Chunk1ParentPath_12_ok,
    tttLargeFiber20Block1Chunk1ParentPath_13_ok,
    tttLargeFiber20Block1Chunk1ParentPath_14_ok,
    tttLargeFiber20Block1Chunk1ParentPath_15_ok]

def tttLargeFiber20Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block1Chunk1SourcesCheck &&
    tttLargeFiber20Block1Chunk1RowsAudit &&
    tttLargeFiber20Block1Chunk1ParentMapAudit &&
    tttLargeFiber20Block1Chunk1ParentsAudit

theorem tttLargeFiber20Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber20Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block1Chunk1SourcesCheck_ok,
    tttLargeFiber20Block1Chunk1RowsAudit_ok,
    tttLargeFiber20Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber20Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
