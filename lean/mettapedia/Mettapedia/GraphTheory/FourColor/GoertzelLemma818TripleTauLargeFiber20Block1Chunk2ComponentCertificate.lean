import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block1Chunk2Sources : List Nat :=
  [   4736, 4737, 4738, 4739, 4740, 4741, 4742, 4743,
   4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751]

def tttLargeFiber20Row96 : TripleComponentParentRow :=
  tripleRow 4736 4672 141 172 132 140 164 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row97 : TripleComponentParentRow :=
  tripleRow 4737 4673 141 172 133 140 164 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row98 : TripleComponentParentRow :=
  tripleRow 4738 4674 141 172 134 140 164 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row99 : TripleComponentParentRow :=
  tripleRow 4739 4675 141 172 135 140 164 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row100 : TripleComponentParentRow :=
  tripleRow 4740 4676 141 172 180 140 164 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row101 : TripleComponentParentRow :=
  tripleRow 4741 4677 141 172 181 140 164 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row102 : TripleComponentParentRow :=
  tripleRow 4742 4678 141 172 182 140 164 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row103 : TripleComponentParentRow :=
  tripleRow 4743 4679 141 172 183 140 164 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row104 : TripleComponentParentRow :=
  tripleRow 4744 4680 141 173 140 140 165 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row105 : TripleComponentParentRow :=
  tripleRow 4745 4681 141 173 141 140 165 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row106 : TripleComponentParentRow :=
  tripleRow 4746 4682 141 173 142 140 165 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row107 : TripleComponentParentRow :=
  tripleRow 4747 4683 141 173 143 140 165 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row108 : TripleComponentParentRow :=
  tripleRow 4748 4684 141 173 188 140 165 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row109 : TripleComponentParentRow :=
  tripleRow 4749 4685 141 173 189 140 165 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row110 : TripleComponentParentRow :=
  tripleRow 4750 4686 141 173 190 140 165 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Row111 : TripleComponentParentRow :=
  tripleRow 4751 4687 141 173 191 140 165 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber20Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row96
  , tttLargeFiber20Row97
  , tttLargeFiber20Row98
  , tttLargeFiber20Row99
  , tttLargeFiber20Row100
  , tttLargeFiber20Row101
  , tttLargeFiber20Row102
  , tttLargeFiber20Row103
  , tttLargeFiber20Row104
  , tttLargeFiber20Row105
  , tttLargeFiber20Row106
  , tttLargeFiber20Row107
  , tttLargeFiber20Row108
  , tttLargeFiber20Row109
  , tttLargeFiber20Row110
  , tttLargeFiber20Row111
  ]

def tttLargeFiber20Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber20Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber20Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber20Block1Chunk2Sources

theorem tttLargeFiber20Block1Chunk2SourcesCheck_ok :
    tttLargeFiber20Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber20Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block1Chunk2RowValid
    (listGetD tttLargeFiber20Block1Chunk2Rows i default)

def tttLargeFiber20Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block1Chunk2Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block1Chunk2Sources 0 0 == 4736
      && tttLargeFiber20ParentOf 4736 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block1Chunk2Sources 1 0 == 4737
      && tttLargeFiber20ParentOf 4737 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block1Chunk2Sources 2 0 == 4738
      && tttLargeFiber20ParentOf 4738 == 4674
      && tttLargeFiber20ParentOf 4674 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block1Chunk2Sources 3 0 == 4739
      && tttLargeFiber20ParentOf 4739 == 4675
      && tttLargeFiber20ParentOf 4675 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block1Chunk2Sources 4 0 == 4740
      && tttLargeFiber20ParentOf 4740 == 4676
      && tttLargeFiber20ParentOf 4676 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block1Chunk2Sources 5 0 == 4741
      && tttLargeFiber20ParentOf 4741 == 4677
      && tttLargeFiber20ParentOf 4677 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block1Chunk2Sources 6 0 == 4742
      && tttLargeFiber20ParentOf 4742 == 4678
      && tttLargeFiber20ParentOf 4678 == 4646
      && tttLargeFiber20ParentOf 4646 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block1Chunk2Sources 7 0 == 4743
      && tttLargeFiber20ParentOf 4743 == 4679
      && tttLargeFiber20ParentOf 4679 == 4647
      && tttLargeFiber20ParentOf 4647 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block1Chunk2Sources 8 0 == 4744
      && tttLargeFiber20ParentOf 4744 == 4680
      && tttLargeFiber20ParentOf 4680 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block1Chunk2Sources 9 0 == 4745
      && tttLargeFiber20ParentOf 4745 == 4681
      && tttLargeFiber20ParentOf 4681 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block1Chunk2Sources 10 0 == 4746
      && tttLargeFiber20ParentOf 4746 == 4682
      && tttLargeFiber20ParentOf 4682 == 4650
      && tttLargeFiber20ParentOf 4650 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block1Chunk2Sources 11 0 == 4747
      && tttLargeFiber20ParentOf 4747 == 4683
      && tttLargeFiber20ParentOf 4683 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block1Chunk2Sources 12 0 == 4748
      && tttLargeFiber20ParentOf 4748 == 4684
      && tttLargeFiber20ParentOf 4684 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block1Chunk2Sources 13 0 == 4749
      && tttLargeFiber20ParentOf 4749 == 4685
      && tttLargeFiber20ParentOf 4685 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block1Chunk2Sources 14 0 == 4750
      && tttLargeFiber20ParentOf 4750 == 4686
      && tttLargeFiber20ParentOf 4686 == 4654
      && tttLargeFiber20ParentOf 4654 == 4646
      && tttLargeFiber20ParentOf 4646 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block1Chunk2Sources 15 0 == 4751
      && tttLargeFiber20ParentOf 4751 == 4687
      && tttLargeFiber20ParentOf 4687 == 4655
      && tttLargeFiber20ParentOf 4655 == 4647
      && tttLargeFiber20ParentOf 4647 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block1Chunk2Row_0_ok :
    tttLargeFiber20Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_1_ok :
    tttLargeFiber20Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_2_ok :
    tttLargeFiber20Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_3_ok :
    tttLargeFiber20Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_4_ok :
    tttLargeFiber20Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_5_ok :
    tttLargeFiber20Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_6_ok :
    tttLargeFiber20Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_7_ok :
    tttLargeFiber20Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_8_ok :
    tttLargeFiber20Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_9_ok :
    tttLargeFiber20Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_10_ok :
    tttLargeFiber20Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_11_ok :
    tttLargeFiber20Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_12_ok :
    tttLargeFiber20Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_13_ok :
    tttLargeFiber20Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_14_ok :
    tttLargeFiber20Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2Row_15_ok :
    tttLargeFiber20Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_0_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_1_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_2_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_3_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_4_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_5_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_6_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_7_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_8_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_9_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_10_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_11_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_12_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_13_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_14_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentMap_15_ok :
    tttLargeFiber20Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_0_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_1_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_2_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_3_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_4_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_5_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_6_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_7_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_8_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_9_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_10_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_11_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_12_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_13_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_14_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block1Chunk2ParentPath_15_ok :
    tttLargeFiber20Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber20Block1Chunk2RowCheck 0
    && tttLargeFiber20Block1Chunk2RowCheck 1
    && tttLargeFiber20Block1Chunk2RowCheck 2
    && tttLargeFiber20Block1Chunk2RowCheck 3
    && tttLargeFiber20Block1Chunk2RowCheck 4
    && tttLargeFiber20Block1Chunk2RowCheck 5
    && tttLargeFiber20Block1Chunk2RowCheck 6
    && tttLargeFiber20Block1Chunk2RowCheck 7
    && tttLargeFiber20Block1Chunk2RowCheck 8
    && tttLargeFiber20Block1Chunk2RowCheck 9
    && tttLargeFiber20Block1Chunk2RowCheck 10
    && tttLargeFiber20Block1Chunk2RowCheck 11
    && tttLargeFiber20Block1Chunk2RowCheck 12
    && tttLargeFiber20Block1Chunk2RowCheck 13
    && tttLargeFiber20Block1Chunk2RowCheck 14
    && tttLargeFiber20Block1Chunk2RowCheck 15

theorem tttLargeFiber20Block1Chunk2RowsAudit_ok :
    tttLargeFiber20Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber20Block1Chunk2RowsAudit,
    tttLargeFiber20Block1Chunk2Row_0_ok,
    tttLargeFiber20Block1Chunk2Row_1_ok,
    tttLargeFiber20Block1Chunk2Row_2_ok,
    tttLargeFiber20Block1Chunk2Row_3_ok,
    tttLargeFiber20Block1Chunk2Row_4_ok,
    tttLargeFiber20Block1Chunk2Row_5_ok,
    tttLargeFiber20Block1Chunk2Row_6_ok,
    tttLargeFiber20Block1Chunk2Row_7_ok,
    tttLargeFiber20Block1Chunk2Row_8_ok,
    tttLargeFiber20Block1Chunk2Row_9_ok,
    tttLargeFiber20Block1Chunk2Row_10_ok,
    tttLargeFiber20Block1Chunk2Row_11_ok,
    tttLargeFiber20Block1Chunk2Row_12_ok,
    tttLargeFiber20Block1Chunk2Row_13_ok,
    tttLargeFiber20Block1Chunk2Row_14_ok,
    tttLargeFiber20Block1Chunk2Row_15_ok]

def tttLargeFiber20Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber20Block1Chunk2ParentMapCheck 0
    && tttLargeFiber20Block1Chunk2ParentMapCheck 1
    && tttLargeFiber20Block1Chunk2ParentMapCheck 2
    && tttLargeFiber20Block1Chunk2ParentMapCheck 3
    && tttLargeFiber20Block1Chunk2ParentMapCheck 4
    && tttLargeFiber20Block1Chunk2ParentMapCheck 5
    && tttLargeFiber20Block1Chunk2ParentMapCheck 6
    && tttLargeFiber20Block1Chunk2ParentMapCheck 7
    && tttLargeFiber20Block1Chunk2ParentMapCheck 8
    && tttLargeFiber20Block1Chunk2ParentMapCheck 9
    && tttLargeFiber20Block1Chunk2ParentMapCheck 10
    && tttLargeFiber20Block1Chunk2ParentMapCheck 11
    && tttLargeFiber20Block1Chunk2ParentMapCheck 12
    && tttLargeFiber20Block1Chunk2ParentMapCheck 13
    && tttLargeFiber20Block1Chunk2ParentMapCheck 14
    && tttLargeFiber20Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber20Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber20Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber20Block1Chunk2ParentMapAudit,
    tttLargeFiber20Block1Chunk2ParentMap_0_ok,
    tttLargeFiber20Block1Chunk2ParentMap_1_ok,
    tttLargeFiber20Block1Chunk2ParentMap_2_ok,
    tttLargeFiber20Block1Chunk2ParentMap_3_ok,
    tttLargeFiber20Block1Chunk2ParentMap_4_ok,
    tttLargeFiber20Block1Chunk2ParentMap_5_ok,
    tttLargeFiber20Block1Chunk2ParentMap_6_ok,
    tttLargeFiber20Block1Chunk2ParentMap_7_ok,
    tttLargeFiber20Block1Chunk2ParentMap_8_ok,
    tttLargeFiber20Block1Chunk2ParentMap_9_ok,
    tttLargeFiber20Block1Chunk2ParentMap_10_ok,
    tttLargeFiber20Block1Chunk2ParentMap_11_ok,
    tttLargeFiber20Block1Chunk2ParentMap_12_ok,
    tttLargeFiber20Block1Chunk2ParentMap_13_ok,
    tttLargeFiber20Block1Chunk2ParentMap_14_ok,
    tttLargeFiber20Block1Chunk2ParentMap_15_ok]

def tttLargeFiber20Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber20Block1Chunk2ParentPathCheck 0
    && tttLargeFiber20Block1Chunk2ParentPathCheck 1
    && tttLargeFiber20Block1Chunk2ParentPathCheck 2
    && tttLargeFiber20Block1Chunk2ParentPathCheck 3
    && tttLargeFiber20Block1Chunk2ParentPathCheck 4
    && tttLargeFiber20Block1Chunk2ParentPathCheck 5
    && tttLargeFiber20Block1Chunk2ParentPathCheck 6
    && tttLargeFiber20Block1Chunk2ParentPathCheck 7
    && tttLargeFiber20Block1Chunk2ParentPathCheck 8
    && tttLargeFiber20Block1Chunk2ParentPathCheck 9
    && tttLargeFiber20Block1Chunk2ParentPathCheck 10
    && tttLargeFiber20Block1Chunk2ParentPathCheck 11
    && tttLargeFiber20Block1Chunk2ParentPathCheck 12
    && tttLargeFiber20Block1Chunk2ParentPathCheck 13
    && tttLargeFiber20Block1Chunk2ParentPathCheck 14
    && tttLargeFiber20Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber20Block1Chunk2ParentsAudit_ok :
    tttLargeFiber20Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber20Block1Chunk2ParentsAudit,
    tttLargeFiber20Block1Chunk2ParentPath_0_ok,
    tttLargeFiber20Block1Chunk2ParentPath_1_ok,
    tttLargeFiber20Block1Chunk2ParentPath_2_ok,
    tttLargeFiber20Block1Chunk2ParentPath_3_ok,
    tttLargeFiber20Block1Chunk2ParentPath_4_ok,
    tttLargeFiber20Block1Chunk2ParentPath_5_ok,
    tttLargeFiber20Block1Chunk2ParentPath_6_ok,
    tttLargeFiber20Block1Chunk2ParentPath_7_ok,
    tttLargeFiber20Block1Chunk2ParentPath_8_ok,
    tttLargeFiber20Block1Chunk2ParentPath_9_ok,
    tttLargeFiber20Block1Chunk2ParentPath_10_ok,
    tttLargeFiber20Block1Chunk2ParentPath_11_ok,
    tttLargeFiber20Block1Chunk2ParentPath_12_ok,
    tttLargeFiber20Block1Chunk2ParentPath_13_ok,
    tttLargeFiber20Block1Chunk2ParentPath_14_ok,
    tttLargeFiber20Block1Chunk2ParentPath_15_ok]

def tttLargeFiber20Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block1Chunk2SourcesCheck &&
    tttLargeFiber20Block1Chunk2RowsAudit &&
    tttLargeFiber20Block1Chunk2ParentMapAudit &&
    tttLargeFiber20Block1Chunk2ParentsAudit

theorem tttLargeFiber20Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber20Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block1Chunk2SourcesCheck_ok,
    tttLargeFiber20Block1Chunk2RowsAudit_ok,
    tttLargeFiber20Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber20Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
