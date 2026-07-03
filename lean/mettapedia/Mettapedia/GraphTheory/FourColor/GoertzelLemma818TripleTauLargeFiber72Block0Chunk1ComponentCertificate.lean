import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block0Chunk1Sources : List Nat :=
  [   832, 833, 834, 835, 836, 837, 838, 839,
   840, 841, 842, 843, 844, 845, 846, 847]

def tttLargeFiber72Row16 : TripleComponentParentRow :=
  tripleRow 832 816 24 82 16 24 80 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row17 : TripleComponentParentRow :=
  tripleRow 833 817 24 82 17 24 80 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row18 : TripleComponentParentRow :=
  tripleRow 834 818 24 82 18 24 80 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row19 : TripleComponentParentRow :=
  tripleRow 835 819 24 82 19 24 80 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row20 : TripleComponentParentRow :=
  tripleRow 836 832 24 82 32 24 82 16
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row21 : TripleComponentParentRow :=
  tripleRow 837 833 24 82 33 24 82 17
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row22 : TripleComponentParentRow :=
  tripleRow 838 822 24 82 34 24 80 102
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

def tttLargeFiber72Row23 : TripleComponentParentRow :=
  tripleRow 839 823 24 82 35 24 80 103
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

def tttLargeFiber72Row24 : TripleComponentParentRow :=
  tripleRow 840 824 24 83 24 24 81 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row25 : TripleComponentParentRow :=
  tripleRow 841 825 24 83 25 24 81 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row26 : TripleComponentParentRow :=
  tripleRow 842 826 24 83 26 24 81 90
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row27 : TripleComponentParentRow :=
  tripleRow 843 827 24 83 27 24 81 91
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row28 : TripleComponentParentRow :=
  tripleRow 844 840 24 83 40 24 83 24
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row29 : TripleComponentParentRow :=
  tripleRow 845 841 24 83 41 24 83 25
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row30 : TripleComponentParentRow :=
  tripleRow 846 830 24 83 42 24 81 110
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

def tttLargeFiber72Row31 : TripleComponentParentRow :=
  tripleRow 847 831 24 83 43 24 81 111
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

def tttLargeFiber72Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row16
  , tttLargeFiber72Row17
  , tttLargeFiber72Row18
  , tttLargeFiber72Row19
  , tttLargeFiber72Row20
  , tttLargeFiber72Row21
  , tttLargeFiber72Row22
  , tttLargeFiber72Row23
  , tttLargeFiber72Row24
  , tttLargeFiber72Row25
  , tttLargeFiber72Row26
  , tttLargeFiber72Row27
  , tttLargeFiber72Row28
  , tttLargeFiber72Row29
  , tttLargeFiber72Row30
  , tttLargeFiber72Row31
  ]

def tttLargeFiber72Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber72Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber72Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber72Block0Chunk1Sources

theorem tttLargeFiber72Block0Chunk1SourcesCheck_ok :
    tttLargeFiber72Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber72Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block0Chunk1RowValid
    (listGetD tttLargeFiber72Block0Chunk1Rows i default)

def tttLargeFiber72Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block0Chunk1Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block0Chunk1Sources 0 0 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (1 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block0Chunk1Sources 1 0 == 833
      && tttLargeFiber72ParentOf 833 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block0Chunk1Sources 2 0 == 834
      && tttLargeFiber72ParentOf 834 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block0Chunk1Sources 3 0 == 835
      && tttLargeFiber72ParentOf 835 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block0Chunk1Sources 4 0 == 836
      && tttLargeFiber72ParentOf 836 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block0Chunk1Sources 5 0 == 837
      && tttLargeFiber72ParentOf 837 == 833
      && tttLargeFiber72ParentOf 833 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block0Chunk1Sources 6 0 == 838
      && tttLargeFiber72ParentOf 838 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block0Chunk1Sources 7 0 == 839
      && tttLargeFiber72ParentOf 839 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block0Chunk1Sources 8 0 == 840
      && tttLargeFiber72ParentOf 840 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block0Chunk1Sources 9 0 == 841
      && tttLargeFiber72ParentOf 841 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block0Chunk1Sources 10 0 == 842
      && tttLargeFiber72ParentOf 842 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block0Chunk1Sources 11 0 == 843
      && tttLargeFiber72ParentOf 843 == 827
      && tttLargeFiber72ParentOf 827 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block0Chunk1Sources 12 0 == 844
      && tttLargeFiber72ParentOf 844 == 840
      && tttLargeFiber72ParentOf 840 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block0Chunk1Sources 13 0 == 845
      && tttLargeFiber72ParentOf 845 == 841
      && tttLargeFiber72ParentOf 841 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block0Chunk1Sources 14 0 == 846
      && tttLargeFiber72ParentOf 846 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block0Chunk1Sources 15 0 == 847
      && tttLargeFiber72ParentOf 847 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block0Chunk1Row_0_ok :
    tttLargeFiber72Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_1_ok :
    tttLargeFiber72Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_2_ok :
    tttLargeFiber72Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_3_ok :
    tttLargeFiber72Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_4_ok :
    tttLargeFiber72Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_5_ok :
    tttLargeFiber72Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_6_ok :
    tttLargeFiber72Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_7_ok :
    tttLargeFiber72Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_8_ok :
    tttLargeFiber72Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_9_ok :
    tttLargeFiber72Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_10_ok :
    tttLargeFiber72Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_11_ok :
    tttLargeFiber72Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_12_ok :
    tttLargeFiber72Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_13_ok :
    tttLargeFiber72Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_14_ok :
    tttLargeFiber72Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1Row_15_ok :
    tttLargeFiber72Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_0_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_1_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_2_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_3_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_4_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_5_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_6_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_7_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_8_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_9_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_10_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_11_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_12_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_13_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_14_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentMap_15_ok :
    tttLargeFiber72Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_0_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_1_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_2_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_3_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_4_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_5_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_6_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_7_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_8_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_9_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_10_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_11_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_12_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_13_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_14_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk1ParentPath_15_ok :
    tttLargeFiber72Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber72Block0Chunk1RowCheck 0
    && tttLargeFiber72Block0Chunk1RowCheck 1
    && tttLargeFiber72Block0Chunk1RowCheck 2
    && tttLargeFiber72Block0Chunk1RowCheck 3
    && tttLargeFiber72Block0Chunk1RowCheck 4
    && tttLargeFiber72Block0Chunk1RowCheck 5
    && tttLargeFiber72Block0Chunk1RowCheck 6
    && tttLargeFiber72Block0Chunk1RowCheck 7
    && tttLargeFiber72Block0Chunk1RowCheck 8
    && tttLargeFiber72Block0Chunk1RowCheck 9
    && tttLargeFiber72Block0Chunk1RowCheck 10
    && tttLargeFiber72Block0Chunk1RowCheck 11
    && tttLargeFiber72Block0Chunk1RowCheck 12
    && tttLargeFiber72Block0Chunk1RowCheck 13
    && tttLargeFiber72Block0Chunk1RowCheck 14
    && tttLargeFiber72Block0Chunk1RowCheck 15

theorem tttLargeFiber72Block0Chunk1RowsAudit_ok :
    tttLargeFiber72Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber72Block0Chunk1RowsAudit,
    tttLargeFiber72Block0Chunk1Row_0_ok,
    tttLargeFiber72Block0Chunk1Row_1_ok,
    tttLargeFiber72Block0Chunk1Row_2_ok,
    tttLargeFiber72Block0Chunk1Row_3_ok,
    tttLargeFiber72Block0Chunk1Row_4_ok,
    tttLargeFiber72Block0Chunk1Row_5_ok,
    tttLargeFiber72Block0Chunk1Row_6_ok,
    tttLargeFiber72Block0Chunk1Row_7_ok,
    tttLargeFiber72Block0Chunk1Row_8_ok,
    tttLargeFiber72Block0Chunk1Row_9_ok,
    tttLargeFiber72Block0Chunk1Row_10_ok,
    tttLargeFiber72Block0Chunk1Row_11_ok,
    tttLargeFiber72Block0Chunk1Row_12_ok,
    tttLargeFiber72Block0Chunk1Row_13_ok,
    tttLargeFiber72Block0Chunk1Row_14_ok,
    tttLargeFiber72Block0Chunk1Row_15_ok]

def tttLargeFiber72Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber72Block0Chunk1ParentMapCheck 0
    && tttLargeFiber72Block0Chunk1ParentMapCheck 1
    && tttLargeFiber72Block0Chunk1ParentMapCheck 2
    && tttLargeFiber72Block0Chunk1ParentMapCheck 3
    && tttLargeFiber72Block0Chunk1ParentMapCheck 4
    && tttLargeFiber72Block0Chunk1ParentMapCheck 5
    && tttLargeFiber72Block0Chunk1ParentMapCheck 6
    && tttLargeFiber72Block0Chunk1ParentMapCheck 7
    && tttLargeFiber72Block0Chunk1ParentMapCheck 8
    && tttLargeFiber72Block0Chunk1ParentMapCheck 9
    && tttLargeFiber72Block0Chunk1ParentMapCheck 10
    && tttLargeFiber72Block0Chunk1ParentMapCheck 11
    && tttLargeFiber72Block0Chunk1ParentMapCheck 12
    && tttLargeFiber72Block0Chunk1ParentMapCheck 13
    && tttLargeFiber72Block0Chunk1ParentMapCheck 14
    && tttLargeFiber72Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber72Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber72Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber72Block0Chunk1ParentMapAudit,
    tttLargeFiber72Block0Chunk1ParentMap_0_ok,
    tttLargeFiber72Block0Chunk1ParentMap_1_ok,
    tttLargeFiber72Block0Chunk1ParentMap_2_ok,
    tttLargeFiber72Block0Chunk1ParentMap_3_ok,
    tttLargeFiber72Block0Chunk1ParentMap_4_ok,
    tttLargeFiber72Block0Chunk1ParentMap_5_ok,
    tttLargeFiber72Block0Chunk1ParentMap_6_ok,
    tttLargeFiber72Block0Chunk1ParentMap_7_ok,
    tttLargeFiber72Block0Chunk1ParentMap_8_ok,
    tttLargeFiber72Block0Chunk1ParentMap_9_ok,
    tttLargeFiber72Block0Chunk1ParentMap_10_ok,
    tttLargeFiber72Block0Chunk1ParentMap_11_ok,
    tttLargeFiber72Block0Chunk1ParentMap_12_ok,
    tttLargeFiber72Block0Chunk1ParentMap_13_ok,
    tttLargeFiber72Block0Chunk1ParentMap_14_ok,
    tttLargeFiber72Block0Chunk1ParentMap_15_ok]

def tttLargeFiber72Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber72Block0Chunk1ParentPathCheck 0
    && tttLargeFiber72Block0Chunk1ParentPathCheck 1
    && tttLargeFiber72Block0Chunk1ParentPathCheck 2
    && tttLargeFiber72Block0Chunk1ParentPathCheck 3
    && tttLargeFiber72Block0Chunk1ParentPathCheck 4
    && tttLargeFiber72Block0Chunk1ParentPathCheck 5
    && tttLargeFiber72Block0Chunk1ParentPathCheck 6
    && tttLargeFiber72Block0Chunk1ParentPathCheck 7
    && tttLargeFiber72Block0Chunk1ParentPathCheck 8
    && tttLargeFiber72Block0Chunk1ParentPathCheck 9
    && tttLargeFiber72Block0Chunk1ParentPathCheck 10
    && tttLargeFiber72Block0Chunk1ParentPathCheck 11
    && tttLargeFiber72Block0Chunk1ParentPathCheck 12
    && tttLargeFiber72Block0Chunk1ParentPathCheck 13
    && tttLargeFiber72Block0Chunk1ParentPathCheck 14
    && tttLargeFiber72Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber72Block0Chunk1ParentsAudit_ok :
    tttLargeFiber72Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber72Block0Chunk1ParentsAudit,
    tttLargeFiber72Block0Chunk1ParentPath_0_ok,
    tttLargeFiber72Block0Chunk1ParentPath_1_ok,
    tttLargeFiber72Block0Chunk1ParentPath_2_ok,
    tttLargeFiber72Block0Chunk1ParentPath_3_ok,
    tttLargeFiber72Block0Chunk1ParentPath_4_ok,
    tttLargeFiber72Block0Chunk1ParentPath_5_ok,
    tttLargeFiber72Block0Chunk1ParentPath_6_ok,
    tttLargeFiber72Block0Chunk1ParentPath_7_ok,
    tttLargeFiber72Block0Chunk1ParentPath_8_ok,
    tttLargeFiber72Block0Chunk1ParentPath_9_ok,
    tttLargeFiber72Block0Chunk1ParentPath_10_ok,
    tttLargeFiber72Block0Chunk1ParentPath_11_ok,
    tttLargeFiber72Block0Chunk1ParentPath_12_ok,
    tttLargeFiber72Block0Chunk1ParentPath_13_ok,
    tttLargeFiber72Block0Chunk1ParentPath_14_ok,
    tttLargeFiber72Block0Chunk1ParentPath_15_ok]

def tttLargeFiber72Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block0Chunk1SourcesCheck &&
    tttLargeFiber72Block0Chunk1RowsAudit &&
    tttLargeFiber72Block0Chunk1ParentMapAudit &&
    tttLargeFiber72Block0Chunk1ParentsAudit

theorem tttLargeFiber72Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber72Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block0Chunk1SourcesCheck_ok,
    tttLargeFiber72Block0Chunk1RowsAudit_ok,
    tttLargeFiber72Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber72Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
