import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 2 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block2Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block2Chunk1Sources : List Nat :=
  [   4784, 4785, 4786, 4787, 4788, 4789, 4790, 4791,
   4792, 4793, 4794, 4795, 4796, 4797, 4798, 4799]

def tttLargeFiber20Row144 : TripleComponentParentRow :=
  tripleRow 4784 4788 142 2 16 142 2 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row145 : TripleComponentParentRow :=
  tripleRow 4785 4789 142 2 17 142 2 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row146 : TripleComponentParentRow :=
  tripleRow 4786 4740 142 2 18 141 172 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row147 : TripleComponentParentRow :=
  tripleRow 4787 4741 142 2 19 141 172 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row148 : TripleComponentParentRow :=
  tripleRow 4788 4736 142 2 32 141 172 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row149 : TripleComponentParentRow :=
  tripleRow 4789 4737 142 2 33 141 172 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row150 : TripleComponentParentRow :=
  tripleRow 4790 4738 142 2 34 141 172 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row151 : TripleComponentParentRow :=
  tripleRow 4791 4739 142 2 35 141 172 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row152 : TripleComponentParentRow :=
  tripleRow 4792 4796 142 3 24 142 3 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row153 : TripleComponentParentRow :=
  tripleRow 4793 4797 142 3 25 142 3 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row154 : TripleComponentParentRow :=
  tripleRow 4794 4748 142 3 26 141 173 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row155 : TripleComponentParentRow :=
  tripleRow 4795 4749 142 3 27 141 173 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row156 : TripleComponentParentRow :=
  tripleRow 4796 4744 142 3 40 141 173 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row157 : TripleComponentParentRow :=
  tripleRow 4797 4745 142 3 41 141 173 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row158 : TripleComponentParentRow :=
  tripleRow 4798 4746 142 3 42 141 173 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Row159 : TripleComponentParentRow :=
  tripleRow 4799 4747 142 3 43 141 173 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber20Block2Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row144
  , tttLargeFiber20Row145
  , tttLargeFiber20Row146
  , tttLargeFiber20Row147
  , tttLargeFiber20Row148
  , tttLargeFiber20Row149
  , tttLargeFiber20Row150
  , tttLargeFiber20Row151
  , tttLargeFiber20Row152
  , tttLargeFiber20Row153
  , tttLargeFiber20Row154
  , tttLargeFiber20Row155
  , tttLargeFiber20Row156
  , tttLargeFiber20Row157
  , tttLargeFiber20Row158
  , tttLargeFiber20Row159
  ]

def tttLargeFiber20Block2Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block2Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block2Chunk1ExpectedContains row.source &&
    tttLargeFiber20Block2Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block2Chunk1SourcesCheck : Bool :=
  (tttLargeFiber20Block2Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber20Block2Chunk1Sources

theorem tttLargeFiber20Block2Chunk1SourcesCheck_ok :
    tttLargeFiber20Block2Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber20Block2Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block2Chunk1RowValid
    (listGetD tttLargeFiber20Block2Chunk1Rows i default)

def tttLargeFiber20Block2Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block2Chunk1Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block2Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block2Chunk1Sources 0 0 == 4784
      && tttLargeFiber20ParentOf 4784 == 4788
      && tttLargeFiber20ParentOf 4788 == 4736
      && tttLargeFiber20ParentOf 4736 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block2Chunk1Sources 1 0 == 4785
      && tttLargeFiber20ParentOf 4785 == 4789
      && tttLargeFiber20ParentOf 4789 == 4737
      && tttLargeFiber20ParentOf 4737 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block2Chunk1Sources 2 0 == 4786
      && tttLargeFiber20ParentOf 4786 == 4740
      && tttLargeFiber20ParentOf 4740 == 4676
      && tttLargeFiber20ParentOf 4676 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block2Chunk1Sources 3 0 == 4787
      && tttLargeFiber20ParentOf 4787 == 4741
      && tttLargeFiber20ParentOf 4741 == 4677
      && tttLargeFiber20ParentOf 4677 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block2Chunk1Sources 4 0 == 4788
      && tttLargeFiber20ParentOf 4788 == 4736
      && tttLargeFiber20ParentOf 4736 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block2Chunk1Sources 5 0 == 4789
      && tttLargeFiber20ParentOf 4789 == 4737
      && tttLargeFiber20ParentOf 4737 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block2Chunk1Sources 6 0 == 4790
      && tttLargeFiber20ParentOf 4790 == 4738
      && tttLargeFiber20ParentOf 4738 == 4674
      && tttLargeFiber20ParentOf 4674 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block2Chunk1Sources 7 0 == 4791
      && tttLargeFiber20ParentOf 4791 == 4739
      && tttLargeFiber20ParentOf 4739 == 4675
      && tttLargeFiber20ParentOf 4675 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block2Chunk1Sources 8 0 == 4792
      && tttLargeFiber20ParentOf 4792 == 4796
      && tttLargeFiber20ParentOf 4796 == 4744
      && tttLargeFiber20ParentOf 4744 == 4680
      && tttLargeFiber20ParentOf 4680 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block2Chunk1Sources 9 0 == 4793
      && tttLargeFiber20ParentOf 4793 == 4797
      && tttLargeFiber20ParentOf 4797 == 4745
      && tttLargeFiber20ParentOf 4745 == 4681
      && tttLargeFiber20ParentOf 4681 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (6 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block2Chunk1Sources 10 0 == 4794
      && tttLargeFiber20ParentOf 4794 == 4748
      && tttLargeFiber20ParentOf 4748 == 4684
      && tttLargeFiber20ParentOf 4684 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block2Chunk1Sources 11 0 == 4795
      && tttLargeFiber20ParentOf 4795 == 4749
      && tttLargeFiber20ParentOf 4749 == 4685
      && tttLargeFiber20ParentOf 4685 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (6 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block2Chunk1Sources 12 0 == 4796
      && tttLargeFiber20ParentOf 4796 == 4744
      && tttLargeFiber20ParentOf 4744 == 4680
      && tttLargeFiber20ParentOf 4680 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block2Chunk1Sources 13 0 == 4797
      && tttLargeFiber20ParentOf 4797 == 4745
      && tttLargeFiber20ParentOf 4745 == 4681
      && tttLargeFiber20ParentOf 4681 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block2Chunk1Sources 14 0 == 4798
      && tttLargeFiber20ParentOf 4798 == 4746
      && tttLargeFiber20ParentOf 4746 == 4682
      && tttLargeFiber20ParentOf 4682 == 4650
      && tttLargeFiber20ParentOf 4650 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (6 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block2Chunk1Sources 15 0 == 4799
      && tttLargeFiber20ParentOf 4799 == 4747
      && tttLargeFiber20ParentOf 4747 == 4683
      && tttLargeFiber20ParentOf 4683 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block2Chunk1Row_0_ok :
    tttLargeFiber20Block2Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_1_ok :
    tttLargeFiber20Block2Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_2_ok :
    tttLargeFiber20Block2Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_3_ok :
    tttLargeFiber20Block2Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_4_ok :
    tttLargeFiber20Block2Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_5_ok :
    tttLargeFiber20Block2Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_6_ok :
    tttLargeFiber20Block2Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_7_ok :
    tttLargeFiber20Block2Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_8_ok :
    tttLargeFiber20Block2Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_9_ok :
    tttLargeFiber20Block2Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_10_ok :
    tttLargeFiber20Block2Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_11_ok :
    tttLargeFiber20Block2Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_12_ok :
    tttLargeFiber20Block2Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_13_ok :
    tttLargeFiber20Block2Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_14_ok :
    tttLargeFiber20Block2Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1Row_15_ok :
    tttLargeFiber20Block2Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_0_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_1_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_2_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_3_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_4_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_5_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_6_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_7_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_8_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_9_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_10_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_11_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_12_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_13_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_14_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentMap_15_ok :
    tttLargeFiber20Block2Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_0_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_1_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_2_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_3_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_4_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_5_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_6_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_7_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_8_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_9_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_10_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_11_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_12_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_13_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_14_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block2Chunk1ParentPath_15_ok :
    tttLargeFiber20Block2Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block2Chunk1RowsAudit : Bool :=
  tttLargeFiber20Block2Chunk1RowCheck 0
    && tttLargeFiber20Block2Chunk1RowCheck 1
    && tttLargeFiber20Block2Chunk1RowCheck 2
    && tttLargeFiber20Block2Chunk1RowCheck 3
    && tttLargeFiber20Block2Chunk1RowCheck 4
    && tttLargeFiber20Block2Chunk1RowCheck 5
    && tttLargeFiber20Block2Chunk1RowCheck 6
    && tttLargeFiber20Block2Chunk1RowCheck 7
    && tttLargeFiber20Block2Chunk1RowCheck 8
    && tttLargeFiber20Block2Chunk1RowCheck 9
    && tttLargeFiber20Block2Chunk1RowCheck 10
    && tttLargeFiber20Block2Chunk1RowCheck 11
    && tttLargeFiber20Block2Chunk1RowCheck 12
    && tttLargeFiber20Block2Chunk1RowCheck 13
    && tttLargeFiber20Block2Chunk1RowCheck 14
    && tttLargeFiber20Block2Chunk1RowCheck 15

theorem tttLargeFiber20Block2Chunk1RowsAudit_ok :
    tttLargeFiber20Block2Chunk1RowsAudit = true := by
  simp [tttLargeFiber20Block2Chunk1RowsAudit,
    tttLargeFiber20Block2Chunk1Row_0_ok,
    tttLargeFiber20Block2Chunk1Row_1_ok,
    tttLargeFiber20Block2Chunk1Row_2_ok,
    tttLargeFiber20Block2Chunk1Row_3_ok,
    tttLargeFiber20Block2Chunk1Row_4_ok,
    tttLargeFiber20Block2Chunk1Row_5_ok,
    tttLargeFiber20Block2Chunk1Row_6_ok,
    tttLargeFiber20Block2Chunk1Row_7_ok,
    tttLargeFiber20Block2Chunk1Row_8_ok,
    tttLargeFiber20Block2Chunk1Row_9_ok,
    tttLargeFiber20Block2Chunk1Row_10_ok,
    tttLargeFiber20Block2Chunk1Row_11_ok,
    tttLargeFiber20Block2Chunk1Row_12_ok,
    tttLargeFiber20Block2Chunk1Row_13_ok,
    tttLargeFiber20Block2Chunk1Row_14_ok,
    tttLargeFiber20Block2Chunk1Row_15_ok]

def tttLargeFiber20Block2Chunk1ParentMapAudit : Bool :=
  tttLargeFiber20Block2Chunk1ParentMapCheck 0
    && tttLargeFiber20Block2Chunk1ParentMapCheck 1
    && tttLargeFiber20Block2Chunk1ParentMapCheck 2
    && tttLargeFiber20Block2Chunk1ParentMapCheck 3
    && tttLargeFiber20Block2Chunk1ParentMapCheck 4
    && tttLargeFiber20Block2Chunk1ParentMapCheck 5
    && tttLargeFiber20Block2Chunk1ParentMapCheck 6
    && tttLargeFiber20Block2Chunk1ParentMapCheck 7
    && tttLargeFiber20Block2Chunk1ParentMapCheck 8
    && tttLargeFiber20Block2Chunk1ParentMapCheck 9
    && tttLargeFiber20Block2Chunk1ParentMapCheck 10
    && tttLargeFiber20Block2Chunk1ParentMapCheck 11
    && tttLargeFiber20Block2Chunk1ParentMapCheck 12
    && tttLargeFiber20Block2Chunk1ParentMapCheck 13
    && tttLargeFiber20Block2Chunk1ParentMapCheck 14
    && tttLargeFiber20Block2Chunk1ParentMapCheck 15

theorem tttLargeFiber20Block2Chunk1ParentMapAudit_ok :
    tttLargeFiber20Block2Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber20Block2Chunk1ParentMapAudit,
    tttLargeFiber20Block2Chunk1ParentMap_0_ok,
    tttLargeFiber20Block2Chunk1ParentMap_1_ok,
    tttLargeFiber20Block2Chunk1ParentMap_2_ok,
    tttLargeFiber20Block2Chunk1ParentMap_3_ok,
    tttLargeFiber20Block2Chunk1ParentMap_4_ok,
    tttLargeFiber20Block2Chunk1ParentMap_5_ok,
    tttLargeFiber20Block2Chunk1ParentMap_6_ok,
    tttLargeFiber20Block2Chunk1ParentMap_7_ok,
    tttLargeFiber20Block2Chunk1ParentMap_8_ok,
    tttLargeFiber20Block2Chunk1ParentMap_9_ok,
    tttLargeFiber20Block2Chunk1ParentMap_10_ok,
    tttLargeFiber20Block2Chunk1ParentMap_11_ok,
    tttLargeFiber20Block2Chunk1ParentMap_12_ok,
    tttLargeFiber20Block2Chunk1ParentMap_13_ok,
    tttLargeFiber20Block2Chunk1ParentMap_14_ok,
    tttLargeFiber20Block2Chunk1ParentMap_15_ok]

def tttLargeFiber20Block2Chunk1ParentsAudit : Bool :=
  tttLargeFiber20Block2Chunk1ParentPathCheck 0
    && tttLargeFiber20Block2Chunk1ParentPathCheck 1
    && tttLargeFiber20Block2Chunk1ParentPathCheck 2
    && tttLargeFiber20Block2Chunk1ParentPathCheck 3
    && tttLargeFiber20Block2Chunk1ParentPathCheck 4
    && tttLargeFiber20Block2Chunk1ParentPathCheck 5
    && tttLargeFiber20Block2Chunk1ParentPathCheck 6
    && tttLargeFiber20Block2Chunk1ParentPathCheck 7
    && tttLargeFiber20Block2Chunk1ParentPathCheck 8
    && tttLargeFiber20Block2Chunk1ParentPathCheck 9
    && tttLargeFiber20Block2Chunk1ParentPathCheck 10
    && tttLargeFiber20Block2Chunk1ParentPathCheck 11
    && tttLargeFiber20Block2Chunk1ParentPathCheck 12
    && tttLargeFiber20Block2Chunk1ParentPathCheck 13
    && tttLargeFiber20Block2Chunk1ParentPathCheck 14
    && tttLargeFiber20Block2Chunk1ParentPathCheck 15

theorem tttLargeFiber20Block2Chunk1ParentsAudit_ok :
    tttLargeFiber20Block2Chunk1ParentsAudit = true := by
  simp [tttLargeFiber20Block2Chunk1ParentsAudit,
    tttLargeFiber20Block2Chunk1ParentPath_0_ok,
    tttLargeFiber20Block2Chunk1ParentPath_1_ok,
    tttLargeFiber20Block2Chunk1ParentPath_2_ok,
    tttLargeFiber20Block2Chunk1ParentPath_3_ok,
    tttLargeFiber20Block2Chunk1ParentPath_4_ok,
    tttLargeFiber20Block2Chunk1ParentPath_5_ok,
    tttLargeFiber20Block2Chunk1ParentPath_6_ok,
    tttLargeFiber20Block2Chunk1ParentPath_7_ok,
    tttLargeFiber20Block2Chunk1ParentPath_8_ok,
    tttLargeFiber20Block2Chunk1ParentPath_9_ok,
    tttLargeFiber20Block2Chunk1ParentPath_10_ok,
    tttLargeFiber20Block2Chunk1ParentPath_11_ok,
    tttLargeFiber20Block2Chunk1ParentPath_12_ok,
    tttLargeFiber20Block2Chunk1ParentPath_13_ok,
    tttLargeFiber20Block2Chunk1ParentPath_14_ok,
    tttLargeFiber20Block2Chunk1ParentPath_15_ok]

def tttLargeFiber20Block2Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block2Chunk1SourcesCheck &&
    tttLargeFiber20Block2Chunk1RowsAudit &&
    tttLargeFiber20Block2Chunk1ParentMapAudit &&
    tttLargeFiber20Block2Chunk1ParentsAudit

theorem tttLargeFiber20Block2Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber20Block2Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block2Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block2Chunk1SourcesCheck_ok,
    tttLargeFiber20Block2Chunk1RowsAudit_ok,
    tttLargeFiber20Block2Chunk1ParentMapAudit_ok,
    tttLargeFiber20Block2Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block2Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
