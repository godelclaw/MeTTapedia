import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 3 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block3Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block3Chunk1Sources : List Nat :=
  [   4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855,
   4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863]

def tttLargeFiber20Row208 : TripleComponentParentRow :=
  tripleRow 4848 4852 143 10 16 143 10 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row209 : TripleComponentParentRow :=
  tripleRow 4849 4853 143 10 17 143 10 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row210 : TripleComponentParentRow :=
  tripleRow 4850 4676 143 10 18 140 164 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber20Row211 : TripleComponentParentRow :=
  tripleRow 4851 4677 143 10 19 140 164 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber20Row212 : TripleComponentParentRow :=
  tripleRow 4852 4672 143 10 32 140 164 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Row213 : TripleComponentParentRow :=
  tripleRow 4853 4673 143 10 33 140 164 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Row214 : TripleComponentParentRow :=
  tripleRow 4854 4674 143 10 34 140 164 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Row215 : TripleComponentParentRow :=
  tripleRow 4855 4675 143 10 35 140 164 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Row216 : TripleComponentParentRow :=
  tripleRow 4856 4860 143 11 24 143 11 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row217 : TripleComponentParentRow :=
  tripleRow 4857 4861 143 11 25 143 11 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row218 : TripleComponentParentRow :=
  tripleRow 4858 4684 143 11 26 140 165 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber20Row219 : TripleComponentParentRow :=
  tripleRow 4859 4685 143 11 27 140 165 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber20Row220 : TripleComponentParentRow :=
  tripleRow 4860 4680 143 11 40 140 165 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Row221 : TripleComponentParentRow :=
  tripleRow 4861 4681 143 11 41 140 165 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Row222 : TripleComponentParentRow :=
  tripleRow 4862 4682 143 11 42 140 165 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Row223 : TripleComponentParentRow :=
  tripleRow 4863 4683 143 11 43 140 165 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber20Block3Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row208
  , tttLargeFiber20Row209
  , tttLargeFiber20Row210
  , tttLargeFiber20Row211
  , tttLargeFiber20Row212
  , tttLargeFiber20Row213
  , tttLargeFiber20Row214
  , tttLargeFiber20Row215
  , tttLargeFiber20Row216
  , tttLargeFiber20Row217
  , tttLargeFiber20Row218
  , tttLargeFiber20Row219
  , tttLargeFiber20Row220
  , tttLargeFiber20Row221
  , tttLargeFiber20Row222
  , tttLargeFiber20Row223
  ]

def tttLargeFiber20Block3Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block3Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block3Chunk1ExpectedContains row.source &&
    tttLargeFiber20Block3Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block3Chunk1SourcesCheck : Bool :=
  (tttLargeFiber20Block3Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber20Block3Chunk1Sources

theorem tttLargeFiber20Block3Chunk1SourcesCheck_ok :
    tttLargeFiber20Block3Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber20Block3Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block3Chunk1RowValid
    (listGetD tttLargeFiber20Block3Chunk1Rows i default)

def tttLargeFiber20Block3Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block3Chunk1Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block3Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block3Chunk1Sources 0 0 == 4848
      && tttLargeFiber20ParentOf 4848 == 4852
      && tttLargeFiber20ParentOf 4852 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block3Chunk1Sources 1 0 == 4849
      && tttLargeFiber20ParentOf 4849 == 4853
      && tttLargeFiber20ParentOf 4853 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block3Chunk1Sources 2 0 == 4850
      && tttLargeFiber20ParentOf 4850 == 4676
      && tttLargeFiber20ParentOf 4676 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block3Chunk1Sources 3 0 == 4851
      && tttLargeFiber20ParentOf 4851 == 4677
      && tttLargeFiber20ParentOf 4677 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block3Chunk1Sources 4 0 == 4852
      && tttLargeFiber20ParentOf 4852 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block3Chunk1Sources 5 0 == 4853
      && tttLargeFiber20ParentOf 4853 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block3Chunk1Sources 6 0 == 4854
      && tttLargeFiber20ParentOf 4854 == 4674
      && tttLargeFiber20ParentOf 4674 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block3Chunk1Sources 7 0 == 4855
      && tttLargeFiber20ParentOf 4855 == 4675
      && tttLargeFiber20ParentOf 4675 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block3Chunk1Sources 8 0 == 4856
      && tttLargeFiber20ParentOf 4856 == 4860
      && tttLargeFiber20ParentOf 4860 == 4680
      && tttLargeFiber20ParentOf 4680 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block3Chunk1Sources 9 0 == 4857
      && tttLargeFiber20ParentOf 4857 == 4861
      && tttLargeFiber20ParentOf 4861 == 4681
      && tttLargeFiber20ParentOf 4681 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block3Chunk1Sources 10 0 == 4858
      && tttLargeFiber20ParentOf 4858 == 4684
      && tttLargeFiber20ParentOf 4684 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block3Chunk1Sources 11 0 == 4859
      && tttLargeFiber20ParentOf 4859 == 4685
      && tttLargeFiber20ParentOf 4685 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block3Chunk1Sources 12 0 == 4860
      && tttLargeFiber20ParentOf 4860 == 4680
      && tttLargeFiber20ParentOf 4680 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block3Chunk1Sources 13 0 == 4861
      && tttLargeFiber20ParentOf 4861 == 4681
      && tttLargeFiber20ParentOf 4681 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block3Chunk1Sources 14 0 == 4862
      && tttLargeFiber20ParentOf 4862 == 4682
      && tttLargeFiber20ParentOf 4682 == 4650
      && tttLargeFiber20ParentOf 4650 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block3Chunk1Sources 15 0 == 4863
      && tttLargeFiber20ParentOf 4863 == 4683
      && tttLargeFiber20ParentOf 4683 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block3Chunk1Row_0_ok :
    tttLargeFiber20Block3Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_1_ok :
    tttLargeFiber20Block3Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_2_ok :
    tttLargeFiber20Block3Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_3_ok :
    tttLargeFiber20Block3Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_4_ok :
    tttLargeFiber20Block3Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_5_ok :
    tttLargeFiber20Block3Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_6_ok :
    tttLargeFiber20Block3Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_7_ok :
    tttLargeFiber20Block3Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_8_ok :
    tttLargeFiber20Block3Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_9_ok :
    tttLargeFiber20Block3Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_10_ok :
    tttLargeFiber20Block3Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_11_ok :
    tttLargeFiber20Block3Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_12_ok :
    tttLargeFiber20Block3Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_13_ok :
    tttLargeFiber20Block3Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_14_ok :
    tttLargeFiber20Block3Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1Row_15_ok :
    tttLargeFiber20Block3Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_0_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_1_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_2_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_3_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_4_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_5_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_6_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_7_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_8_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_9_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_10_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_11_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_12_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_13_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_14_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentMap_15_ok :
    tttLargeFiber20Block3Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_0_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_1_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_2_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_3_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_4_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_5_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_6_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_7_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_8_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_9_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_10_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_11_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_12_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_13_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_14_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block3Chunk1ParentPath_15_ok :
    tttLargeFiber20Block3Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block3Chunk1RowsAudit : Bool :=
  tttLargeFiber20Block3Chunk1RowCheck 0
    && tttLargeFiber20Block3Chunk1RowCheck 1
    && tttLargeFiber20Block3Chunk1RowCheck 2
    && tttLargeFiber20Block3Chunk1RowCheck 3
    && tttLargeFiber20Block3Chunk1RowCheck 4
    && tttLargeFiber20Block3Chunk1RowCheck 5
    && tttLargeFiber20Block3Chunk1RowCheck 6
    && tttLargeFiber20Block3Chunk1RowCheck 7
    && tttLargeFiber20Block3Chunk1RowCheck 8
    && tttLargeFiber20Block3Chunk1RowCheck 9
    && tttLargeFiber20Block3Chunk1RowCheck 10
    && tttLargeFiber20Block3Chunk1RowCheck 11
    && tttLargeFiber20Block3Chunk1RowCheck 12
    && tttLargeFiber20Block3Chunk1RowCheck 13
    && tttLargeFiber20Block3Chunk1RowCheck 14
    && tttLargeFiber20Block3Chunk1RowCheck 15

theorem tttLargeFiber20Block3Chunk1RowsAudit_ok :
    tttLargeFiber20Block3Chunk1RowsAudit = true := by
  simp [tttLargeFiber20Block3Chunk1RowsAudit,
    tttLargeFiber20Block3Chunk1Row_0_ok,
    tttLargeFiber20Block3Chunk1Row_1_ok,
    tttLargeFiber20Block3Chunk1Row_2_ok,
    tttLargeFiber20Block3Chunk1Row_3_ok,
    tttLargeFiber20Block3Chunk1Row_4_ok,
    tttLargeFiber20Block3Chunk1Row_5_ok,
    tttLargeFiber20Block3Chunk1Row_6_ok,
    tttLargeFiber20Block3Chunk1Row_7_ok,
    tttLargeFiber20Block3Chunk1Row_8_ok,
    tttLargeFiber20Block3Chunk1Row_9_ok,
    tttLargeFiber20Block3Chunk1Row_10_ok,
    tttLargeFiber20Block3Chunk1Row_11_ok,
    tttLargeFiber20Block3Chunk1Row_12_ok,
    tttLargeFiber20Block3Chunk1Row_13_ok,
    tttLargeFiber20Block3Chunk1Row_14_ok,
    tttLargeFiber20Block3Chunk1Row_15_ok]

def tttLargeFiber20Block3Chunk1ParentMapAudit : Bool :=
  tttLargeFiber20Block3Chunk1ParentMapCheck 0
    && tttLargeFiber20Block3Chunk1ParentMapCheck 1
    && tttLargeFiber20Block3Chunk1ParentMapCheck 2
    && tttLargeFiber20Block3Chunk1ParentMapCheck 3
    && tttLargeFiber20Block3Chunk1ParentMapCheck 4
    && tttLargeFiber20Block3Chunk1ParentMapCheck 5
    && tttLargeFiber20Block3Chunk1ParentMapCheck 6
    && tttLargeFiber20Block3Chunk1ParentMapCheck 7
    && tttLargeFiber20Block3Chunk1ParentMapCheck 8
    && tttLargeFiber20Block3Chunk1ParentMapCheck 9
    && tttLargeFiber20Block3Chunk1ParentMapCheck 10
    && tttLargeFiber20Block3Chunk1ParentMapCheck 11
    && tttLargeFiber20Block3Chunk1ParentMapCheck 12
    && tttLargeFiber20Block3Chunk1ParentMapCheck 13
    && tttLargeFiber20Block3Chunk1ParentMapCheck 14
    && tttLargeFiber20Block3Chunk1ParentMapCheck 15

theorem tttLargeFiber20Block3Chunk1ParentMapAudit_ok :
    tttLargeFiber20Block3Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber20Block3Chunk1ParentMapAudit,
    tttLargeFiber20Block3Chunk1ParentMap_0_ok,
    tttLargeFiber20Block3Chunk1ParentMap_1_ok,
    tttLargeFiber20Block3Chunk1ParentMap_2_ok,
    tttLargeFiber20Block3Chunk1ParentMap_3_ok,
    tttLargeFiber20Block3Chunk1ParentMap_4_ok,
    tttLargeFiber20Block3Chunk1ParentMap_5_ok,
    tttLargeFiber20Block3Chunk1ParentMap_6_ok,
    tttLargeFiber20Block3Chunk1ParentMap_7_ok,
    tttLargeFiber20Block3Chunk1ParentMap_8_ok,
    tttLargeFiber20Block3Chunk1ParentMap_9_ok,
    tttLargeFiber20Block3Chunk1ParentMap_10_ok,
    tttLargeFiber20Block3Chunk1ParentMap_11_ok,
    tttLargeFiber20Block3Chunk1ParentMap_12_ok,
    tttLargeFiber20Block3Chunk1ParentMap_13_ok,
    tttLargeFiber20Block3Chunk1ParentMap_14_ok,
    tttLargeFiber20Block3Chunk1ParentMap_15_ok]

def tttLargeFiber20Block3Chunk1ParentsAudit : Bool :=
  tttLargeFiber20Block3Chunk1ParentPathCheck 0
    && tttLargeFiber20Block3Chunk1ParentPathCheck 1
    && tttLargeFiber20Block3Chunk1ParentPathCheck 2
    && tttLargeFiber20Block3Chunk1ParentPathCheck 3
    && tttLargeFiber20Block3Chunk1ParentPathCheck 4
    && tttLargeFiber20Block3Chunk1ParentPathCheck 5
    && tttLargeFiber20Block3Chunk1ParentPathCheck 6
    && tttLargeFiber20Block3Chunk1ParentPathCheck 7
    && tttLargeFiber20Block3Chunk1ParentPathCheck 8
    && tttLargeFiber20Block3Chunk1ParentPathCheck 9
    && tttLargeFiber20Block3Chunk1ParentPathCheck 10
    && tttLargeFiber20Block3Chunk1ParentPathCheck 11
    && tttLargeFiber20Block3Chunk1ParentPathCheck 12
    && tttLargeFiber20Block3Chunk1ParentPathCheck 13
    && tttLargeFiber20Block3Chunk1ParentPathCheck 14
    && tttLargeFiber20Block3Chunk1ParentPathCheck 15

theorem tttLargeFiber20Block3Chunk1ParentsAudit_ok :
    tttLargeFiber20Block3Chunk1ParentsAudit = true := by
  simp [tttLargeFiber20Block3Chunk1ParentsAudit,
    tttLargeFiber20Block3Chunk1ParentPath_0_ok,
    tttLargeFiber20Block3Chunk1ParentPath_1_ok,
    tttLargeFiber20Block3Chunk1ParentPath_2_ok,
    tttLargeFiber20Block3Chunk1ParentPath_3_ok,
    tttLargeFiber20Block3Chunk1ParentPath_4_ok,
    tttLargeFiber20Block3Chunk1ParentPath_5_ok,
    tttLargeFiber20Block3Chunk1ParentPath_6_ok,
    tttLargeFiber20Block3Chunk1ParentPath_7_ok,
    tttLargeFiber20Block3Chunk1ParentPath_8_ok,
    tttLargeFiber20Block3Chunk1ParentPath_9_ok,
    tttLargeFiber20Block3Chunk1ParentPath_10_ok,
    tttLargeFiber20Block3Chunk1ParentPath_11_ok,
    tttLargeFiber20Block3Chunk1ParentPath_12_ok,
    tttLargeFiber20Block3Chunk1ParentPath_13_ok,
    tttLargeFiber20Block3Chunk1ParentPath_14_ok,
    tttLargeFiber20Block3Chunk1ParentPath_15_ok]

def tttLargeFiber20Block3Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block3Chunk1SourcesCheck &&
    tttLargeFiber20Block3Chunk1RowsAudit &&
    tttLargeFiber20Block3Chunk1ParentMapAudit &&
    tttLargeFiber20Block3Chunk1ParentsAudit

theorem tttLargeFiber20Block3Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber20Block3Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block3Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block3Chunk1SourcesCheck_ok,
    tttLargeFiber20Block3Chunk1RowsAudit_ok,
    tttLargeFiber20Block3Chunk1ParentMapAudit_ok,
    tttLargeFiber20Block3Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block3Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
