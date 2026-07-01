import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block1Chunk3Sources : List Nat :=
  [   4752, 4753, 4754, 4755, 4756, 4757, 4758, 4759,
   4760, 4761, 4762, 4763, 4764, 4765, 4766, 4767]

def tttLargeFiber20Row112 : TripleComponentParentRow :=
  tripleRow 4752 4688 141 174 64 140 166 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row113 : TripleComponentParentRow :=
  tripleRow 4753 4689 141 174 65 140 166 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row114 : TripleComponentParentRow :=
  tripleRow 4754 4690 141 174 66 140 166 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row115 : TripleComponentParentRow :=
  tripleRow 4755 4691 141 174 67 140 166 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row116 : TripleComponentParentRow :=
  tripleRow 4756 4692 141 174 116 140 166 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row117 : TripleComponentParentRow :=
  tripleRow 4757 4693 141 174 117 140 166 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row118 : TripleComponentParentRow :=
  tripleRow 4758 4694 141 174 118 140 166 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row119 : TripleComponentParentRow :=
  tripleRow 4759 4695 141 174 119 140 166 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row120 : TripleComponentParentRow :=
  tripleRow 4760 4696 141 175 72 140 167 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row121 : TripleComponentParentRow :=
  tripleRow 4761 4697 141 175 73 140 167 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row122 : TripleComponentParentRow :=
  tripleRow 4762 4698 141 175 74 140 167 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row123 : TripleComponentParentRow :=
  tripleRow 4763 4699 141 175 75 140 167 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row124 : TripleComponentParentRow :=
  tripleRow 4764 4700 141 175 124 140 167 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row125 : TripleComponentParentRow :=
  tripleRow 4765 4701 141 175 125 140 167 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row126 : TripleComponentParentRow :=
  tripleRow 4766 4702 141 175 126 140 167 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row127 : TripleComponentParentRow :=
  tripleRow 4767 4703 141 175 127 140 167 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row112
  , tttLargeFiber20Row113
  , tttLargeFiber20Row114
  , tttLargeFiber20Row115
  , tttLargeFiber20Row116
  , tttLargeFiber20Row117
  , tttLargeFiber20Row118
  , tttLargeFiber20Row119
  , tttLargeFiber20Row120
  , tttLargeFiber20Row121
  , tttLargeFiber20Row122
  , tttLargeFiber20Row123
  , tttLargeFiber20Row124
  , tttLargeFiber20Row125
  , tttLargeFiber20Row126
  , tttLargeFiber20Row127
  ]

def tttLargeFiber20Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber20Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber20Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber20Block1Chunk3Sources

theorem tttLargeFiber20Block1Chunk3SourcesCheck_ok :
    tttLargeFiber20Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber20Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block1Chunk3RowValid
    (listGetD tttLargeFiber20Block1Chunk3Rows i default)

def tttLargeFiber20Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block1Chunk3Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block1Chunk3Sources 0 0 == 4752
      && tttLargeFiber20ParentOf 4752 == 4688
      && tttLargeFiber20ParentOf 4688 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block1Chunk3Sources 1 0 == 4753
      && tttLargeFiber20ParentOf 4753 == 4689
      && tttLargeFiber20ParentOf 4689 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block1Chunk3Sources 2 0 == 4754
      && tttLargeFiber20ParentOf 4754 == 4690
      && tttLargeFiber20ParentOf 4690 == 4688
      && tttLargeFiber20ParentOf 4688 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block1Chunk3Sources 3 0 == 4755
      && tttLargeFiber20ParentOf 4755 == 4691
      && tttLargeFiber20ParentOf 4691 == 4675
      && tttLargeFiber20ParentOf 4675 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block1Chunk3Sources 4 0 == 4756
      && tttLargeFiber20ParentOf 4756 == 4692
      && tttLargeFiber20ParentOf 4692 == 4676
      && tttLargeFiber20ParentOf 4676 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block1Chunk3Sources 5 0 == 4757
      && tttLargeFiber20ParentOf 4757 == 4693
      && tttLargeFiber20ParentOf 4693 == 4677
      && tttLargeFiber20ParentOf 4677 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block1Chunk3Sources 6 0 == 4758
      && tttLargeFiber20ParentOf 4758 == 4694
      && tttLargeFiber20ParentOf 4694 == 4689
      && tttLargeFiber20ParentOf 4689 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block1Chunk3Sources 7 0 == 4759
      && tttLargeFiber20ParentOf 4759 == 4695
      && tttLargeFiber20ParentOf 4695 == 4688
      && tttLargeFiber20ParentOf 4688 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block1Chunk3Sources 8 0 == 4760
      && tttLargeFiber20ParentOf 4760 == 4696
      && tttLargeFiber20ParentOf 4696 == 4680
      && tttLargeFiber20ParentOf 4680 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block1Chunk3Sources 9 0 == 4761
      && tttLargeFiber20ParentOf 4761 == 4697
      && tttLargeFiber20ParentOf 4697 == 4681
      && tttLargeFiber20ParentOf 4681 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block1Chunk3Sources 10 0 == 4762
      && tttLargeFiber20ParentOf 4762 == 4698
      && tttLargeFiber20ParentOf 4698 == 4666
      && tttLargeFiber20ParentOf 4666 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block1Chunk3Sources 11 0 == 4763
      && tttLargeFiber20ParentOf 4763 == 4699
      && tttLargeFiber20ParentOf 4699 == 4667
      && tttLargeFiber20ParentOf 4667 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block1Chunk3Sources 12 0 == 4764
      && tttLargeFiber20ParentOf 4764 == 4700
      && tttLargeFiber20ParentOf 4700 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block1Chunk3Sources 13 0 == 4765
      && tttLargeFiber20ParentOf 4765 == 4701
      && tttLargeFiber20ParentOf 4701 == 4669
      && tttLargeFiber20ParentOf 4669 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block1Chunk3Sources 14 0 == 4766
      && tttLargeFiber20ParentOf 4766 == 4702
      && tttLargeFiber20ParentOf 4702 == 4700
      && tttLargeFiber20ParentOf 4700 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block1Chunk3Sources 15 0 == 4767
      && tttLargeFiber20ParentOf 4767 == 4703
      && tttLargeFiber20ParentOf 4703 == 4671
      && tttLargeFiber20ParentOf 4671 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block1Chunk3Row_0_ok :
    tttLargeFiber20Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_1_ok :
    tttLargeFiber20Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_2_ok :
    tttLargeFiber20Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_3_ok :
    tttLargeFiber20Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_4_ok :
    tttLargeFiber20Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_5_ok :
    tttLargeFiber20Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_6_ok :
    tttLargeFiber20Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_7_ok :
    tttLargeFiber20Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_8_ok :
    tttLargeFiber20Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_9_ok :
    tttLargeFiber20Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_10_ok :
    tttLargeFiber20Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_11_ok :
    tttLargeFiber20Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_12_ok :
    tttLargeFiber20Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_13_ok :
    tttLargeFiber20Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_14_ok :
    tttLargeFiber20Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3Row_15_ok :
    tttLargeFiber20Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_0_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_1_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_2_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_3_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_4_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_5_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_6_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_7_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_8_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_9_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_10_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_11_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_12_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_13_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_14_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentMap_15_ok :
    tttLargeFiber20Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_0_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_1_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_2_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_3_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_4_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_5_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_6_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_7_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_8_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_9_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_10_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_11_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_12_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_13_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_14_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk3ParentPath_15_ok :
    tttLargeFiber20Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber20Block1Chunk3RowCheck 0
    && tttLargeFiber20Block1Chunk3RowCheck 1
    && tttLargeFiber20Block1Chunk3RowCheck 2
    && tttLargeFiber20Block1Chunk3RowCheck 3
    && tttLargeFiber20Block1Chunk3RowCheck 4
    && tttLargeFiber20Block1Chunk3RowCheck 5
    && tttLargeFiber20Block1Chunk3RowCheck 6
    && tttLargeFiber20Block1Chunk3RowCheck 7
    && tttLargeFiber20Block1Chunk3RowCheck 8
    && tttLargeFiber20Block1Chunk3RowCheck 9
    && tttLargeFiber20Block1Chunk3RowCheck 10
    && tttLargeFiber20Block1Chunk3RowCheck 11
    && tttLargeFiber20Block1Chunk3RowCheck 12
    && tttLargeFiber20Block1Chunk3RowCheck 13
    && tttLargeFiber20Block1Chunk3RowCheck 14
    && tttLargeFiber20Block1Chunk3RowCheck 15

theorem tttLargeFiber20Block1Chunk3RowsAudit_ok :
    tttLargeFiber20Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber20Block1Chunk3RowsAudit,
    tttLargeFiber20Block1Chunk3Row_0_ok,
    tttLargeFiber20Block1Chunk3Row_1_ok,
    tttLargeFiber20Block1Chunk3Row_2_ok,
    tttLargeFiber20Block1Chunk3Row_3_ok,
    tttLargeFiber20Block1Chunk3Row_4_ok,
    tttLargeFiber20Block1Chunk3Row_5_ok,
    tttLargeFiber20Block1Chunk3Row_6_ok,
    tttLargeFiber20Block1Chunk3Row_7_ok,
    tttLargeFiber20Block1Chunk3Row_8_ok,
    tttLargeFiber20Block1Chunk3Row_9_ok,
    tttLargeFiber20Block1Chunk3Row_10_ok,
    tttLargeFiber20Block1Chunk3Row_11_ok,
    tttLargeFiber20Block1Chunk3Row_12_ok,
    tttLargeFiber20Block1Chunk3Row_13_ok,
    tttLargeFiber20Block1Chunk3Row_14_ok,
    tttLargeFiber20Block1Chunk3Row_15_ok]

def tttLargeFiber20Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber20Block1Chunk3ParentMapCheck 0
    && tttLargeFiber20Block1Chunk3ParentMapCheck 1
    && tttLargeFiber20Block1Chunk3ParentMapCheck 2
    && tttLargeFiber20Block1Chunk3ParentMapCheck 3
    && tttLargeFiber20Block1Chunk3ParentMapCheck 4
    && tttLargeFiber20Block1Chunk3ParentMapCheck 5
    && tttLargeFiber20Block1Chunk3ParentMapCheck 6
    && tttLargeFiber20Block1Chunk3ParentMapCheck 7
    && tttLargeFiber20Block1Chunk3ParentMapCheck 8
    && tttLargeFiber20Block1Chunk3ParentMapCheck 9
    && tttLargeFiber20Block1Chunk3ParentMapCheck 10
    && tttLargeFiber20Block1Chunk3ParentMapCheck 11
    && tttLargeFiber20Block1Chunk3ParentMapCheck 12
    && tttLargeFiber20Block1Chunk3ParentMapCheck 13
    && tttLargeFiber20Block1Chunk3ParentMapCheck 14
    && tttLargeFiber20Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber20Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber20Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber20Block1Chunk3ParentMapAudit,
    tttLargeFiber20Block1Chunk3ParentMap_0_ok,
    tttLargeFiber20Block1Chunk3ParentMap_1_ok,
    tttLargeFiber20Block1Chunk3ParentMap_2_ok,
    tttLargeFiber20Block1Chunk3ParentMap_3_ok,
    tttLargeFiber20Block1Chunk3ParentMap_4_ok,
    tttLargeFiber20Block1Chunk3ParentMap_5_ok,
    tttLargeFiber20Block1Chunk3ParentMap_6_ok,
    tttLargeFiber20Block1Chunk3ParentMap_7_ok,
    tttLargeFiber20Block1Chunk3ParentMap_8_ok,
    tttLargeFiber20Block1Chunk3ParentMap_9_ok,
    tttLargeFiber20Block1Chunk3ParentMap_10_ok,
    tttLargeFiber20Block1Chunk3ParentMap_11_ok,
    tttLargeFiber20Block1Chunk3ParentMap_12_ok,
    tttLargeFiber20Block1Chunk3ParentMap_13_ok,
    tttLargeFiber20Block1Chunk3ParentMap_14_ok,
    tttLargeFiber20Block1Chunk3ParentMap_15_ok]

def tttLargeFiber20Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber20Block1Chunk3ParentPathCheck 0
    && tttLargeFiber20Block1Chunk3ParentPathCheck 1
    && tttLargeFiber20Block1Chunk3ParentPathCheck 2
    && tttLargeFiber20Block1Chunk3ParentPathCheck 3
    && tttLargeFiber20Block1Chunk3ParentPathCheck 4
    && tttLargeFiber20Block1Chunk3ParentPathCheck 5
    && tttLargeFiber20Block1Chunk3ParentPathCheck 6
    && tttLargeFiber20Block1Chunk3ParentPathCheck 7
    && tttLargeFiber20Block1Chunk3ParentPathCheck 8
    && tttLargeFiber20Block1Chunk3ParentPathCheck 9
    && tttLargeFiber20Block1Chunk3ParentPathCheck 10
    && tttLargeFiber20Block1Chunk3ParentPathCheck 11
    && tttLargeFiber20Block1Chunk3ParentPathCheck 12
    && tttLargeFiber20Block1Chunk3ParentPathCheck 13
    && tttLargeFiber20Block1Chunk3ParentPathCheck 14
    && tttLargeFiber20Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber20Block1Chunk3ParentsAudit_ok :
    tttLargeFiber20Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber20Block1Chunk3ParentsAudit,
    tttLargeFiber20Block1Chunk3ParentPath_0_ok,
    tttLargeFiber20Block1Chunk3ParentPath_1_ok,
    tttLargeFiber20Block1Chunk3ParentPath_2_ok,
    tttLargeFiber20Block1Chunk3ParentPath_3_ok,
    tttLargeFiber20Block1Chunk3ParentPath_4_ok,
    tttLargeFiber20Block1Chunk3ParentPath_5_ok,
    tttLargeFiber20Block1Chunk3ParentPath_6_ok,
    tttLargeFiber20Block1Chunk3ParentPath_7_ok,
    tttLargeFiber20Block1Chunk3ParentPath_8_ok,
    tttLargeFiber20Block1Chunk3ParentPath_9_ok,
    tttLargeFiber20Block1Chunk3ParentPath_10_ok,
    tttLargeFiber20Block1Chunk3ParentPath_11_ok,
    tttLargeFiber20Block1Chunk3ParentPath_12_ok,
    tttLargeFiber20Block1Chunk3ParentPath_13_ok,
    tttLargeFiber20Block1Chunk3ParentPath_14_ok,
    tttLargeFiber20Block1Chunk3ParentPath_15_ok]

def tttLargeFiber20Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block1Chunk3SourcesCheck &&
    tttLargeFiber20Block1Chunk3RowsAudit &&
    tttLargeFiber20Block1Chunk3ParentMapAudit &&
    tttLargeFiber20Block1Chunk3ParentsAudit

theorem tttLargeFiber20Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber20Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block1Chunk3SourcesCheck_ok,
    tttLargeFiber20Block1Chunk3RowsAudit_ok,
    tttLargeFiber20Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber20Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
