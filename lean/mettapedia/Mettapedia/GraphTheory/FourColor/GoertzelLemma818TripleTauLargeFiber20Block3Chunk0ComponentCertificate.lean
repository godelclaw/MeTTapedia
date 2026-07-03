import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 3 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block3Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block3Chunk0Sources : List Nat :=
  [   4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839,
   4840, 4841, 4842, 4843, 4844, 4845, 4846, 4847]

def tttLargeFiber20Row192 : TripleComponentParentRow :=
  tripleRow 4832 4864 143 8 80 143 56 148
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

def tttLargeFiber20Row193 : TripleComponentParentRow :=
  tripleRow 4833 4865 143 8 81 143 56 149
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

def tttLargeFiber20Row194 : TripleComponentParentRow :=
  tripleRow 4834 4832 143 8 82 143 8 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row195 : TripleComponentParentRow :=
  tripleRow 4835 4867 143 8 83 143 56 151
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

def tttLargeFiber20Row196 : TripleComponentParentRow :=
  tripleRow 4836 4868 143 8 100 143 56 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row197 : TripleComponentParentRow :=
  tripleRow 4837 4869 143 8 101 143 56 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row198 : TripleComponentParentRow :=
  tripleRow 4838 4833 143 8 102 143 8 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row199 : TripleComponentParentRow :=
  tripleRow 4839 4832 143 8 103 143 8 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row200 : TripleComponentParentRow :=
  tripleRow 4840 4872 143 9 88 143 57 156
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

def tttLargeFiber20Row201 : TripleComponentParentRow :=
  tripleRow 4841 4873 143 9 89 143 57 157
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

def tttLargeFiber20Row202 : TripleComponentParentRow :=
  tripleRow 4842 4840 143 9 90 143 9 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row203 : TripleComponentParentRow :=
  tripleRow 4843 4875 143 9 91 143 57 159
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

def tttLargeFiber20Row204 : TripleComponentParentRow :=
  tripleRow 4844 4876 143 9 108 143 57 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row205 : TripleComponentParentRow :=
  tripleRow 4845 4877 143 9 109 143 57 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row206 : TripleComponentParentRow :=
  tripleRow 4846 4841 143 9 110 143 9 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row207 : TripleComponentParentRow :=
  tripleRow 4847 4840 143 9 111 143 9 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Block3Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row192
  , tttLargeFiber20Row193
  , tttLargeFiber20Row194
  , tttLargeFiber20Row195
  , tttLargeFiber20Row196
  , tttLargeFiber20Row197
  , tttLargeFiber20Row198
  , tttLargeFiber20Row199
  , tttLargeFiber20Row200
  , tttLargeFiber20Row201
  , tttLargeFiber20Row202
  , tttLargeFiber20Row203
  , tttLargeFiber20Row204
  , tttLargeFiber20Row205
  , tttLargeFiber20Row206
  , tttLargeFiber20Row207
  ]

def tttLargeFiber20Block3Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block3Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block3Chunk0ExpectedContains row.source &&
    tttLargeFiber20Block3Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block3Chunk0SourcesCheck : Bool :=
  (tttLargeFiber20Block3Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber20Block3Chunk0Sources

theorem tttLargeFiber20Block3Chunk0SourcesCheck_ok :
    tttLargeFiber20Block3Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber20Block3Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block3Chunk0RowValid
    (listGetD tttLargeFiber20Block3Chunk0Rows i default)

def tttLargeFiber20Block3Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block3Chunk0Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block3Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block3Chunk0Sources 0 0 == 4832
      && tttLargeFiber20ParentOf 4832 == 4864
      && tttLargeFiber20ParentOf 4864 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block3Chunk0Sources 1 0 == 4833
      && tttLargeFiber20ParentOf 4833 == 4865
      && tttLargeFiber20ParentOf 4865 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block3Chunk0Sources 2 0 == 4834
      && tttLargeFiber20ParentOf 4834 == 4832
      && tttLargeFiber20ParentOf 4832 == 4864
      && tttLargeFiber20ParentOf 4864 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block3Chunk0Sources 3 0 == 4835
      && tttLargeFiber20ParentOf 4835 == 4867
      && tttLargeFiber20ParentOf 4867 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block3Chunk0Sources 4 0 == 4836
      && tttLargeFiber20ParentOf 4836 == 4868
      && tttLargeFiber20ParentOf 4868 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block3Chunk0Sources 5 0 == 4837
      && tttLargeFiber20ParentOf 4837 == 4869
      && tttLargeFiber20ParentOf 4869 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block3Chunk0Sources 6 0 == 4838
      && tttLargeFiber20ParentOf 4838 == 4833
      && tttLargeFiber20ParentOf 4833 == 4865
      && tttLargeFiber20ParentOf 4865 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block3Chunk0Sources 7 0 == 4839
      && tttLargeFiber20ParentOf 4839 == 4832
      && tttLargeFiber20ParentOf 4832 == 4864
      && tttLargeFiber20ParentOf 4864 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block3Chunk0Sources 8 0 == 4840
      && tttLargeFiber20ParentOf 4840 == 4872
      && tttLargeFiber20ParentOf 4872 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block3Chunk0Sources 9 0 == 4841
      && tttLargeFiber20ParentOf 4841 == 4873
      && tttLargeFiber20ParentOf 4873 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block3Chunk0Sources 10 0 == 4842
      && tttLargeFiber20ParentOf 4842 == 4840
      && tttLargeFiber20ParentOf 4840 == 4872
      && tttLargeFiber20ParentOf 4872 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block3Chunk0Sources 11 0 == 4843
      && tttLargeFiber20ParentOf 4843 == 4875
      && tttLargeFiber20ParentOf 4875 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block3Chunk0Sources 12 0 == 4844
      && tttLargeFiber20ParentOf 4844 == 4876
      && tttLargeFiber20ParentOf 4876 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block3Chunk0Sources 13 0 == 4845
      && tttLargeFiber20ParentOf 4845 == 4877
      && tttLargeFiber20ParentOf 4877 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block3Chunk0Sources 14 0 == 4846
      && tttLargeFiber20ParentOf 4846 == 4841
      && tttLargeFiber20ParentOf 4841 == 4873
      && tttLargeFiber20ParentOf 4873 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block3Chunk0Sources 15 0 == 4847
      && tttLargeFiber20ParentOf 4847 == 4840
      && tttLargeFiber20ParentOf 4840 == 4872
      && tttLargeFiber20ParentOf 4872 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block3Chunk0Row_0_ok :
    tttLargeFiber20Block3Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_1_ok :
    tttLargeFiber20Block3Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_2_ok :
    tttLargeFiber20Block3Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_3_ok :
    tttLargeFiber20Block3Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_4_ok :
    tttLargeFiber20Block3Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_5_ok :
    tttLargeFiber20Block3Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_6_ok :
    tttLargeFiber20Block3Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_7_ok :
    tttLargeFiber20Block3Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_8_ok :
    tttLargeFiber20Block3Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_9_ok :
    tttLargeFiber20Block3Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_10_ok :
    tttLargeFiber20Block3Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_11_ok :
    tttLargeFiber20Block3Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_12_ok :
    tttLargeFiber20Block3Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_13_ok :
    tttLargeFiber20Block3Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_14_ok :
    tttLargeFiber20Block3Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0Row_15_ok :
    tttLargeFiber20Block3Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_0_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_1_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_2_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_3_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_4_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_5_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_6_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_7_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_8_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_9_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_10_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_11_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_12_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_13_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_14_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentMap_15_ok :
    tttLargeFiber20Block3Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_0_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_1_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_2_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_3_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_4_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_5_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_6_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_7_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_8_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_9_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_10_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_11_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_12_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_13_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_14_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block3Chunk0ParentPath_15_ok :
    tttLargeFiber20Block3Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block3Chunk0RowsAudit : Bool :=
  tttLargeFiber20Block3Chunk0RowCheck 0
    && tttLargeFiber20Block3Chunk0RowCheck 1
    && tttLargeFiber20Block3Chunk0RowCheck 2
    && tttLargeFiber20Block3Chunk0RowCheck 3
    && tttLargeFiber20Block3Chunk0RowCheck 4
    && tttLargeFiber20Block3Chunk0RowCheck 5
    && tttLargeFiber20Block3Chunk0RowCheck 6
    && tttLargeFiber20Block3Chunk0RowCheck 7
    && tttLargeFiber20Block3Chunk0RowCheck 8
    && tttLargeFiber20Block3Chunk0RowCheck 9
    && tttLargeFiber20Block3Chunk0RowCheck 10
    && tttLargeFiber20Block3Chunk0RowCheck 11
    && tttLargeFiber20Block3Chunk0RowCheck 12
    && tttLargeFiber20Block3Chunk0RowCheck 13
    && tttLargeFiber20Block3Chunk0RowCheck 14
    && tttLargeFiber20Block3Chunk0RowCheck 15

theorem tttLargeFiber20Block3Chunk0RowsAudit_ok :
    tttLargeFiber20Block3Chunk0RowsAudit = true := by
  simp [tttLargeFiber20Block3Chunk0RowsAudit,
    tttLargeFiber20Block3Chunk0Row_0_ok,
    tttLargeFiber20Block3Chunk0Row_1_ok,
    tttLargeFiber20Block3Chunk0Row_2_ok,
    tttLargeFiber20Block3Chunk0Row_3_ok,
    tttLargeFiber20Block3Chunk0Row_4_ok,
    tttLargeFiber20Block3Chunk0Row_5_ok,
    tttLargeFiber20Block3Chunk0Row_6_ok,
    tttLargeFiber20Block3Chunk0Row_7_ok,
    tttLargeFiber20Block3Chunk0Row_8_ok,
    tttLargeFiber20Block3Chunk0Row_9_ok,
    tttLargeFiber20Block3Chunk0Row_10_ok,
    tttLargeFiber20Block3Chunk0Row_11_ok,
    tttLargeFiber20Block3Chunk0Row_12_ok,
    tttLargeFiber20Block3Chunk0Row_13_ok,
    tttLargeFiber20Block3Chunk0Row_14_ok,
    tttLargeFiber20Block3Chunk0Row_15_ok]

def tttLargeFiber20Block3Chunk0ParentMapAudit : Bool :=
  tttLargeFiber20Block3Chunk0ParentMapCheck 0
    && tttLargeFiber20Block3Chunk0ParentMapCheck 1
    && tttLargeFiber20Block3Chunk0ParentMapCheck 2
    && tttLargeFiber20Block3Chunk0ParentMapCheck 3
    && tttLargeFiber20Block3Chunk0ParentMapCheck 4
    && tttLargeFiber20Block3Chunk0ParentMapCheck 5
    && tttLargeFiber20Block3Chunk0ParentMapCheck 6
    && tttLargeFiber20Block3Chunk0ParentMapCheck 7
    && tttLargeFiber20Block3Chunk0ParentMapCheck 8
    && tttLargeFiber20Block3Chunk0ParentMapCheck 9
    && tttLargeFiber20Block3Chunk0ParentMapCheck 10
    && tttLargeFiber20Block3Chunk0ParentMapCheck 11
    && tttLargeFiber20Block3Chunk0ParentMapCheck 12
    && tttLargeFiber20Block3Chunk0ParentMapCheck 13
    && tttLargeFiber20Block3Chunk0ParentMapCheck 14
    && tttLargeFiber20Block3Chunk0ParentMapCheck 15

theorem tttLargeFiber20Block3Chunk0ParentMapAudit_ok :
    tttLargeFiber20Block3Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber20Block3Chunk0ParentMapAudit,
    tttLargeFiber20Block3Chunk0ParentMap_0_ok,
    tttLargeFiber20Block3Chunk0ParentMap_1_ok,
    tttLargeFiber20Block3Chunk0ParentMap_2_ok,
    tttLargeFiber20Block3Chunk0ParentMap_3_ok,
    tttLargeFiber20Block3Chunk0ParentMap_4_ok,
    tttLargeFiber20Block3Chunk0ParentMap_5_ok,
    tttLargeFiber20Block3Chunk0ParentMap_6_ok,
    tttLargeFiber20Block3Chunk0ParentMap_7_ok,
    tttLargeFiber20Block3Chunk0ParentMap_8_ok,
    tttLargeFiber20Block3Chunk0ParentMap_9_ok,
    tttLargeFiber20Block3Chunk0ParentMap_10_ok,
    tttLargeFiber20Block3Chunk0ParentMap_11_ok,
    tttLargeFiber20Block3Chunk0ParentMap_12_ok,
    tttLargeFiber20Block3Chunk0ParentMap_13_ok,
    tttLargeFiber20Block3Chunk0ParentMap_14_ok,
    tttLargeFiber20Block3Chunk0ParentMap_15_ok]

def tttLargeFiber20Block3Chunk0ParentsAudit : Bool :=
  tttLargeFiber20Block3Chunk0ParentPathCheck 0
    && tttLargeFiber20Block3Chunk0ParentPathCheck 1
    && tttLargeFiber20Block3Chunk0ParentPathCheck 2
    && tttLargeFiber20Block3Chunk0ParentPathCheck 3
    && tttLargeFiber20Block3Chunk0ParentPathCheck 4
    && tttLargeFiber20Block3Chunk0ParentPathCheck 5
    && tttLargeFiber20Block3Chunk0ParentPathCheck 6
    && tttLargeFiber20Block3Chunk0ParentPathCheck 7
    && tttLargeFiber20Block3Chunk0ParentPathCheck 8
    && tttLargeFiber20Block3Chunk0ParentPathCheck 9
    && tttLargeFiber20Block3Chunk0ParentPathCheck 10
    && tttLargeFiber20Block3Chunk0ParentPathCheck 11
    && tttLargeFiber20Block3Chunk0ParentPathCheck 12
    && tttLargeFiber20Block3Chunk0ParentPathCheck 13
    && tttLargeFiber20Block3Chunk0ParentPathCheck 14
    && tttLargeFiber20Block3Chunk0ParentPathCheck 15

theorem tttLargeFiber20Block3Chunk0ParentsAudit_ok :
    tttLargeFiber20Block3Chunk0ParentsAudit = true := by
  simp [tttLargeFiber20Block3Chunk0ParentsAudit,
    tttLargeFiber20Block3Chunk0ParentPath_0_ok,
    tttLargeFiber20Block3Chunk0ParentPath_1_ok,
    tttLargeFiber20Block3Chunk0ParentPath_2_ok,
    tttLargeFiber20Block3Chunk0ParentPath_3_ok,
    tttLargeFiber20Block3Chunk0ParentPath_4_ok,
    tttLargeFiber20Block3Chunk0ParentPath_5_ok,
    tttLargeFiber20Block3Chunk0ParentPath_6_ok,
    tttLargeFiber20Block3Chunk0ParentPath_7_ok,
    tttLargeFiber20Block3Chunk0ParentPath_8_ok,
    tttLargeFiber20Block3Chunk0ParentPath_9_ok,
    tttLargeFiber20Block3Chunk0ParentPath_10_ok,
    tttLargeFiber20Block3Chunk0ParentPath_11_ok,
    tttLargeFiber20Block3Chunk0ParentPath_12_ok,
    tttLargeFiber20Block3Chunk0ParentPath_13_ok,
    tttLargeFiber20Block3Chunk0ParentPath_14_ok,
    tttLargeFiber20Block3Chunk0ParentPath_15_ok]

def tttLargeFiber20Block3Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block3Chunk0SourcesCheck &&
    tttLargeFiber20Block3Chunk0RowsAudit &&
    tttLargeFiber20Block3Chunk0ParentMapAudit &&
    tttLargeFiber20Block3Chunk0ParentsAudit

theorem tttLargeFiber20Block3Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber20Block3Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block3Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block3Chunk0SourcesCheck_ok,
    tttLargeFiber20Block3Chunk0RowsAudit_ok,
    tttLargeFiber20Block3Chunk0ParentMapAudit_ok,
    tttLargeFiber20Block3Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block3Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
