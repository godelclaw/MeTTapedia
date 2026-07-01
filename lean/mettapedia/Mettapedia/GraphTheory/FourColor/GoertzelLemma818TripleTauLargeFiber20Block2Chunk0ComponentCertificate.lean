import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 2 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block2Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block2Chunk0Sources : List Nat :=
  [   4768, 4769, 4770, 4771, 4772, 4773, 4774, 4775,
   4776, 4777, 4778, 4779, 4780, 4781, 4782, 4783]

def tttLargeFiber20Row128 : TripleComponentParentRow :=
  tripleRow 4768 4800 142 0 80 142 48 148
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row129 : TripleComponentParentRow :=
  tripleRow 4769 4801 142 0 81 142 48 149
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row130 : TripleComponentParentRow :=
  tripleRow 4770 4768 142 0 82 142 0 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row131 : TripleComponentParentRow :=
  tripleRow 4771 4803 142 0 83 142 48 151
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber20Row132 : TripleComponentParentRow :=
  tripleRow 4772 4804 142 0 100 142 48 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row133 : TripleComponentParentRow :=
  tripleRow 4773 4805 142 0 101 142 48 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row134 : TripleComponentParentRow :=
  tripleRow 4774 4769 142 0 102 142 0 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row135 : TripleComponentParentRow :=
  tripleRow 4775 4768 142 0 103 142 0 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row136 : TripleComponentParentRow :=
  tripleRow 4776 4808 142 1 88 142 49 156
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row137 : TripleComponentParentRow :=
  tripleRow 4777 4809 142 1 89 142 49 157
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row138 : TripleComponentParentRow :=
  tripleRow 4778 4776 142 1 90 142 1 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row139 : TripleComponentParentRow :=
  tripleRow 4779 4811 142 1 91 142 49 159
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber20Row140 : TripleComponentParentRow :=
  tripleRow 4780 4812 142 1 108 142 49 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row141 : TripleComponentParentRow :=
  tripleRow 4781 4813 142 1 109 142 49 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row142 : TripleComponentParentRow :=
  tripleRow 4782 4777 142 1 110 142 1 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row143 : TripleComponentParentRow :=
  tripleRow 4783 4776 142 1 111 142 1 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Block2Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row128
  , tttLargeFiber20Row129
  , tttLargeFiber20Row130
  , tttLargeFiber20Row131
  , tttLargeFiber20Row132
  , tttLargeFiber20Row133
  , tttLargeFiber20Row134
  , tttLargeFiber20Row135
  , tttLargeFiber20Row136
  , tttLargeFiber20Row137
  , tttLargeFiber20Row138
  , tttLargeFiber20Row139
  , tttLargeFiber20Row140
  , tttLargeFiber20Row141
  , tttLargeFiber20Row142
  , tttLargeFiber20Row143
  ]

def tttLargeFiber20Block2Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block2Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block2Chunk0ExpectedContains row.source &&
    tttLargeFiber20Block2Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block2Chunk0SourcesCheck : Bool :=
  (tttLargeFiber20Block2Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber20Block2Chunk0Sources

theorem tttLargeFiber20Block2Chunk0SourcesCheck_ok :
    tttLargeFiber20Block2Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber20Block2Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block2Chunk0RowValid
    (listGetD tttLargeFiber20Block2Chunk0Rows i default)

def tttLargeFiber20Block2Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block2Chunk0Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block2Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block2Chunk0Sources 0 0 == 4768
      && tttLargeFiber20ParentOf 4768 == 4800
      && tttLargeFiber20ParentOf 4800 == 4704
      && tttLargeFiber20ParentOf 4704 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block2Chunk0Sources 1 0 == 4769
      && tttLargeFiber20ParentOf 4769 == 4801
      && tttLargeFiber20ParentOf 4801 == 4705
      && tttLargeFiber20ParentOf 4705 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block2Chunk0Sources 2 0 == 4770
      && tttLargeFiber20ParentOf 4770 == 4768
      && tttLargeFiber20ParentOf 4768 == 4800
      && tttLargeFiber20ParentOf 4800 == 4704
      && tttLargeFiber20ParentOf 4704 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block2Chunk0Sources 3 0 == 4771
      && tttLargeFiber20ParentOf 4771 == 4803
      && tttLargeFiber20ParentOf 4803 == 4707
      && tttLargeFiber20ParentOf 4707 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block2Chunk0Sources 4 0 == 4772
      && tttLargeFiber20ParentOf 4772 == 4804
      && tttLargeFiber20ParentOf 4804 == 4708
      && tttLargeFiber20ParentOf 4708 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block2Chunk0Sources 5 0 == 4773
      && tttLargeFiber20ParentOf 4773 == 4805
      && tttLargeFiber20ParentOf 4805 == 4709
      && tttLargeFiber20ParentOf 4709 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block2Chunk0Sources 6 0 == 4774
      && tttLargeFiber20ParentOf 4774 == 4769
      && tttLargeFiber20ParentOf 4769 == 4801
      && tttLargeFiber20ParentOf 4801 == 4705
      && tttLargeFiber20ParentOf 4705 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block2Chunk0Sources 7 0 == 4775
      && tttLargeFiber20ParentOf 4775 == 4768
      && tttLargeFiber20ParentOf 4768 == 4800
      && tttLargeFiber20ParentOf 4800 == 4704
      && tttLargeFiber20ParentOf 4704 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block2Chunk0Sources 8 0 == 4776
      && tttLargeFiber20ParentOf 4776 == 4808
      && tttLargeFiber20ParentOf 4808 == 4712
      && tttLargeFiber20ParentOf 4712 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block2Chunk0Sources 9 0 == 4777
      && tttLargeFiber20ParentOf 4777 == 4809
      && tttLargeFiber20ParentOf 4809 == 4713
      && tttLargeFiber20ParentOf 4713 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block2Chunk0Sources 10 0 == 4778
      && tttLargeFiber20ParentOf 4778 == 4776
      && tttLargeFiber20ParentOf 4776 == 4808
      && tttLargeFiber20ParentOf 4808 == 4712
      && tttLargeFiber20ParentOf 4712 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block2Chunk0Sources 11 0 == 4779
      && tttLargeFiber20ParentOf 4779 == 4811
      && tttLargeFiber20ParentOf 4811 == 4715
      && tttLargeFiber20ParentOf 4715 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block2Chunk0Sources 12 0 == 4780
      && tttLargeFiber20ParentOf 4780 == 4812
      && tttLargeFiber20ParentOf 4812 == 4716
      && tttLargeFiber20ParentOf 4716 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block2Chunk0Sources 13 0 == 4781
      && tttLargeFiber20ParentOf 4781 == 4813
      && tttLargeFiber20ParentOf 4813 == 4717
      && tttLargeFiber20ParentOf 4717 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (6 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block2Chunk0Sources 14 0 == 4782
      && tttLargeFiber20ParentOf 4782 == 4777
      && tttLargeFiber20ParentOf 4777 == 4809
      && tttLargeFiber20ParentOf 4809 == 4713
      && tttLargeFiber20ParentOf 4713 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (6 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block2Chunk0Sources 15 0 == 4783
      && tttLargeFiber20ParentOf 4783 == 4776
      && tttLargeFiber20ParentOf 4776 == 4808
      && tttLargeFiber20ParentOf 4808 == 4712
      && tttLargeFiber20ParentOf 4712 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block2Chunk0Row_0_ok :
    tttLargeFiber20Block2Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_1_ok :
    tttLargeFiber20Block2Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_2_ok :
    tttLargeFiber20Block2Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_3_ok :
    tttLargeFiber20Block2Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_4_ok :
    tttLargeFiber20Block2Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_5_ok :
    tttLargeFiber20Block2Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_6_ok :
    tttLargeFiber20Block2Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_7_ok :
    tttLargeFiber20Block2Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_8_ok :
    tttLargeFiber20Block2Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_9_ok :
    tttLargeFiber20Block2Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_10_ok :
    tttLargeFiber20Block2Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_11_ok :
    tttLargeFiber20Block2Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_12_ok :
    tttLargeFiber20Block2Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_13_ok :
    tttLargeFiber20Block2Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_14_ok :
    tttLargeFiber20Block2Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0Row_15_ok :
    tttLargeFiber20Block2Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_0_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_1_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_2_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_3_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_4_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_5_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_6_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_7_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_8_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_9_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_10_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_11_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_12_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_13_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_14_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentMap_15_ok :
    tttLargeFiber20Block2Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_0_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_1_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_2_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_3_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_4_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_5_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_6_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_7_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_8_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_9_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_10_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_11_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_12_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_13_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_14_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block2Chunk0ParentPath_15_ok :
    tttLargeFiber20Block2Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block2Chunk0RowsAudit : Bool :=
  tttLargeFiber20Block2Chunk0RowCheck 0
    && tttLargeFiber20Block2Chunk0RowCheck 1
    && tttLargeFiber20Block2Chunk0RowCheck 2
    && tttLargeFiber20Block2Chunk0RowCheck 3
    && tttLargeFiber20Block2Chunk0RowCheck 4
    && tttLargeFiber20Block2Chunk0RowCheck 5
    && tttLargeFiber20Block2Chunk0RowCheck 6
    && tttLargeFiber20Block2Chunk0RowCheck 7
    && tttLargeFiber20Block2Chunk0RowCheck 8
    && tttLargeFiber20Block2Chunk0RowCheck 9
    && tttLargeFiber20Block2Chunk0RowCheck 10
    && tttLargeFiber20Block2Chunk0RowCheck 11
    && tttLargeFiber20Block2Chunk0RowCheck 12
    && tttLargeFiber20Block2Chunk0RowCheck 13
    && tttLargeFiber20Block2Chunk0RowCheck 14
    && tttLargeFiber20Block2Chunk0RowCheck 15

theorem tttLargeFiber20Block2Chunk0RowsAudit_ok :
    tttLargeFiber20Block2Chunk0RowsAudit = true := by
  simp [tttLargeFiber20Block2Chunk0RowsAudit,
    tttLargeFiber20Block2Chunk0Row_0_ok,
    tttLargeFiber20Block2Chunk0Row_1_ok,
    tttLargeFiber20Block2Chunk0Row_2_ok,
    tttLargeFiber20Block2Chunk0Row_3_ok,
    tttLargeFiber20Block2Chunk0Row_4_ok,
    tttLargeFiber20Block2Chunk0Row_5_ok,
    tttLargeFiber20Block2Chunk0Row_6_ok,
    tttLargeFiber20Block2Chunk0Row_7_ok,
    tttLargeFiber20Block2Chunk0Row_8_ok,
    tttLargeFiber20Block2Chunk0Row_9_ok,
    tttLargeFiber20Block2Chunk0Row_10_ok,
    tttLargeFiber20Block2Chunk0Row_11_ok,
    tttLargeFiber20Block2Chunk0Row_12_ok,
    tttLargeFiber20Block2Chunk0Row_13_ok,
    tttLargeFiber20Block2Chunk0Row_14_ok,
    tttLargeFiber20Block2Chunk0Row_15_ok]

def tttLargeFiber20Block2Chunk0ParentMapAudit : Bool :=
  tttLargeFiber20Block2Chunk0ParentMapCheck 0
    && tttLargeFiber20Block2Chunk0ParentMapCheck 1
    && tttLargeFiber20Block2Chunk0ParentMapCheck 2
    && tttLargeFiber20Block2Chunk0ParentMapCheck 3
    && tttLargeFiber20Block2Chunk0ParentMapCheck 4
    && tttLargeFiber20Block2Chunk0ParentMapCheck 5
    && tttLargeFiber20Block2Chunk0ParentMapCheck 6
    && tttLargeFiber20Block2Chunk0ParentMapCheck 7
    && tttLargeFiber20Block2Chunk0ParentMapCheck 8
    && tttLargeFiber20Block2Chunk0ParentMapCheck 9
    && tttLargeFiber20Block2Chunk0ParentMapCheck 10
    && tttLargeFiber20Block2Chunk0ParentMapCheck 11
    && tttLargeFiber20Block2Chunk0ParentMapCheck 12
    && tttLargeFiber20Block2Chunk0ParentMapCheck 13
    && tttLargeFiber20Block2Chunk0ParentMapCheck 14
    && tttLargeFiber20Block2Chunk0ParentMapCheck 15

theorem tttLargeFiber20Block2Chunk0ParentMapAudit_ok :
    tttLargeFiber20Block2Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber20Block2Chunk0ParentMapAudit,
    tttLargeFiber20Block2Chunk0ParentMap_0_ok,
    tttLargeFiber20Block2Chunk0ParentMap_1_ok,
    tttLargeFiber20Block2Chunk0ParentMap_2_ok,
    tttLargeFiber20Block2Chunk0ParentMap_3_ok,
    tttLargeFiber20Block2Chunk0ParentMap_4_ok,
    tttLargeFiber20Block2Chunk0ParentMap_5_ok,
    tttLargeFiber20Block2Chunk0ParentMap_6_ok,
    tttLargeFiber20Block2Chunk0ParentMap_7_ok,
    tttLargeFiber20Block2Chunk0ParentMap_8_ok,
    tttLargeFiber20Block2Chunk0ParentMap_9_ok,
    tttLargeFiber20Block2Chunk0ParentMap_10_ok,
    tttLargeFiber20Block2Chunk0ParentMap_11_ok,
    tttLargeFiber20Block2Chunk0ParentMap_12_ok,
    tttLargeFiber20Block2Chunk0ParentMap_13_ok,
    tttLargeFiber20Block2Chunk0ParentMap_14_ok,
    tttLargeFiber20Block2Chunk0ParentMap_15_ok]

def tttLargeFiber20Block2Chunk0ParentsAudit : Bool :=
  tttLargeFiber20Block2Chunk0ParentPathCheck 0
    && tttLargeFiber20Block2Chunk0ParentPathCheck 1
    && tttLargeFiber20Block2Chunk0ParentPathCheck 2
    && tttLargeFiber20Block2Chunk0ParentPathCheck 3
    && tttLargeFiber20Block2Chunk0ParentPathCheck 4
    && tttLargeFiber20Block2Chunk0ParentPathCheck 5
    && tttLargeFiber20Block2Chunk0ParentPathCheck 6
    && tttLargeFiber20Block2Chunk0ParentPathCheck 7
    && tttLargeFiber20Block2Chunk0ParentPathCheck 8
    && tttLargeFiber20Block2Chunk0ParentPathCheck 9
    && tttLargeFiber20Block2Chunk0ParentPathCheck 10
    && tttLargeFiber20Block2Chunk0ParentPathCheck 11
    && tttLargeFiber20Block2Chunk0ParentPathCheck 12
    && tttLargeFiber20Block2Chunk0ParentPathCheck 13
    && tttLargeFiber20Block2Chunk0ParentPathCheck 14
    && tttLargeFiber20Block2Chunk0ParentPathCheck 15

theorem tttLargeFiber20Block2Chunk0ParentsAudit_ok :
    tttLargeFiber20Block2Chunk0ParentsAudit = true := by
  simp [tttLargeFiber20Block2Chunk0ParentsAudit,
    tttLargeFiber20Block2Chunk0ParentPath_0_ok,
    tttLargeFiber20Block2Chunk0ParentPath_1_ok,
    tttLargeFiber20Block2Chunk0ParentPath_2_ok,
    tttLargeFiber20Block2Chunk0ParentPath_3_ok,
    tttLargeFiber20Block2Chunk0ParentPath_4_ok,
    tttLargeFiber20Block2Chunk0ParentPath_5_ok,
    tttLargeFiber20Block2Chunk0ParentPath_6_ok,
    tttLargeFiber20Block2Chunk0ParentPath_7_ok,
    tttLargeFiber20Block2Chunk0ParentPath_8_ok,
    tttLargeFiber20Block2Chunk0ParentPath_9_ok,
    tttLargeFiber20Block2Chunk0ParentPath_10_ok,
    tttLargeFiber20Block2Chunk0ParentPath_11_ok,
    tttLargeFiber20Block2Chunk0ParentPath_12_ok,
    tttLargeFiber20Block2Chunk0ParentPath_13_ok,
    tttLargeFiber20Block2Chunk0ParentPath_14_ok,
    tttLargeFiber20Block2Chunk0ParentPath_15_ok]

def tttLargeFiber20Block2Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block2Chunk0SourcesCheck &&
    tttLargeFiber20Block2Chunk0RowsAudit &&
    tttLargeFiber20Block2Chunk0ParentMapAudit &&
    tttLargeFiber20Block2Chunk0ParentsAudit

theorem tttLargeFiber20Block2Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber20Block2Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block2Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block2Chunk0SourcesCheck_ok,
    tttLargeFiber20Block2Chunk0RowsAudit_ok,
    tttLargeFiber20Block2Chunk0ParentMapAudit_ok,
    tttLargeFiber20Block2Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block2Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
