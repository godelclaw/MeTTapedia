import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block1Chunk1Sources : List Nat :=
  [   896, 897, 898, 899, 900, 901, 902, 903,
   904, 905, 906, 907, 908, 909, 910, 911]

def tttLargeFiber72Row80 : TripleComponentParentRow :=
  tripleRow 896 832 25 90 16 24 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row81 : TripleComponentParentRow :=
  tripleRow 897 833 25 90 17 24 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row82 : TripleComponentParentRow :=
  tripleRow 898 834 25 90 18 24 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row83 : TripleComponentParentRow :=
  tripleRow 899 835 25 90 19 24 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row84 : TripleComponentParentRow :=
  tripleRow 900 836 25 90 32 24 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row85 : TripleComponentParentRow :=
  tripleRow 901 837 25 90 33 24 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row86 : TripleComponentParentRow :=
  tripleRow 902 838 25 90 34 24 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row87 : TripleComponentParentRow :=
  tripleRow 903 839 25 90 35 24 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row88 : TripleComponentParentRow :=
  tripleRow 904 840 25 91 24 24 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row89 : TripleComponentParentRow :=
  tripleRow 905 841 25 91 25 24 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row90 : TripleComponentParentRow :=
  tripleRow 906 842 25 91 26 24 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row91 : TripleComponentParentRow :=
  tripleRow 907 843 25 91 27 24 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row92 : TripleComponentParentRow :=
  tripleRow 908 844 25 91 40 24 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row93 : TripleComponentParentRow :=
  tripleRow 909 845 25 91 41 24 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row94 : TripleComponentParentRow :=
  tripleRow 910 846 25 91 42 24 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row95 : TripleComponentParentRow :=
  tripleRow 911 847 25 91 43 24 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row80
  , tttLargeFiber72Row81
  , tttLargeFiber72Row82
  , tttLargeFiber72Row83
  , tttLargeFiber72Row84
  , tttLargeFiber72Row85
  , tttLargeFiber72Row86
  , tttLargeFiber72Row87
  , tttLargeFiber72Row88
  , tttLargeFiber72Row89
  , tttLargeFiber72Row90
  , tttLargeFiber72Row91
  , tttLargeFiber72Row92
  , tttLargeFiber72Row93
  , tttLargeFiber72Row94
  , tttLargeFiber72Row95
  ]

def tttLargeFiber72Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber72Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber72Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber72Block1Chunk1Sources

theorem tttLargeFiber72Block1Chunk1SourcesCheck_ok :
    tttLargeFiber72Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber72Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block1Chunk1RowValid
    (listGetD tttLargeFiber72Block1Chunk1Rows i default)

def tttLargeFiber72Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block1Chunk1Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block1Chunk1Sources 0 0 == 896
      && tttLargeFiber72ParentOf 896 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block1Chunk1Sources 1 0 == 897
      && tttLargeFiber72ParentOf 897 == 833
      && tttLargeFiber72ParentOf 833 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block1Chunk1Sources 2 0 == 898
      && tttLargeFiber72ParentOf 898 == 834
      && tttLargeFiber72ParentOf 834 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block1Chunk1Sources 3 0 == 899
      && tttLargeFiber72ParentOf 899 == 835
      && tttLargeFiber72ParentOf 835 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block1Chunk1Sources 4 0 == 900
      && tttLargeFiber72ParentOf 900 == 836
      && tttLargeFiber72ParentOf 836 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block1Chunk1Sources 5 0 == 901
      && tttLargeFiber72ParentOf 901 == 837
      && tttLargeFiber72ParentOf 837 == 833
      && tttLargeFiber72ParentOf 833 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block1Chunk1Sources 6 0 == 902
      && tttLargeFiber72ParentOf 902 == 838
      && tttLargeFiber72ParentOf 838 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block1Chunk1Sources 7 0 == 903
      && tttLargeFiber72ParentOf 903 == 839
      && tttLargeFiber72ParentOf 839 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block1Chunk1Sources 8 0 == 904
      && tttLargeFiber72ParentOf 904 == 840
      && tttLargeFiber72ParentOf 840 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block1Chunk1Sources 9 0 == 905
      && tttLargeFiber72ParentOf 905 == 841
      && tttLargeFiber72ParentOf 841 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block1Chunk1Sources 10 0 == 906
      && tttLargeFiber72ParentOf 906 == 842
      && tttLargeFiber72ParentOf 842 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block1Chunk1Sources 11 0 == 907
      && tttLargeFiber72ParentOf 907 == 843
      && tttLargeFiber72ParentOf 843 == 827
      && tttLargeFiber72ParentOf 827 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block1Chunk1Sources 12 0 == 908
      && tttLargeFiber72ParentOf 908 == 844
      && tttLargeFiber72ParentOf 844 == 840
      && tttLargeFiber72ParentOf 840 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block1Chunk1Sources 13 0 == 909
      && tttLargeFiber72ParentOf 909 == 845
      && tttLargeFiber72ParentOf 845 == 841
      && tttLargeFiber72ParentOf 841 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block1Chunk1Sources 14 0 == 910
      && tttLargeFiber72ParentOf 910 == 846
      && tttLargeFiber72ParentOf 846 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block1Chunk1Sources 15 0 == 911
      && tttLargeFiber72ParentOf 911 == 847
      && tttLargeFiber72ParentOf 847 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block1Chunk1Row_0_ok :
    tttLargeFiber72Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_1_ok :
    tttLargeFiber72Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_2_ok :
    tttLargeFiber72Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_3_ok :
    tttLargeFiber72Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_4_ok :
    tttLargeFiber72Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_5_ok :
    tttLargeFiber72Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_6_ok :
    tttLargeFiber72Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_7_ok :
    tttLargeFiber72Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_8_ok :
    tttLargeFiber72Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_9_ok :
    tttLargeFiber72Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_10_ok :
    tttLargeFiber72Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_11_ok :
    tttLargeFiber72Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_12_ok :
    tttLargeFiber72Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_13_ok :
    tttLargeFiber72Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_14_ok :
    tttLargeFiber72Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1Row_15_ok :
    tttLargeFiber72Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_0_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_1_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_2_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_3_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_4_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_5_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_6_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_7_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_8_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_9_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_10_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_11_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_12_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_13_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_14_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentMap_15_ok :
    tttLargeFiber72Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_0_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_1_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_2_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_3_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_4_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_5_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_6_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_7_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_8_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_9_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_10_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_11_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_12_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_13_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_14_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block1Chunk1ParentPath_15_ok :
    tttLargeFiber72Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber72Block1Chunk1RowCheck 0
    && tttLargeFiber72Block1Chunk1RowCheck 1
    && tttLargeFiber72Block1Chunk1RowCheck 2
    && tttLargeFiber72Block1Chunk1RowCheck 3
    && tttLargeFiber72Block1Chunk1RowCheck 4
    && tttLargeFiber72Block1Chunk1RowCheck 5
    && tttLargeFiber72Block1Chunk1RowCheck 6
    && tttLargeFiber72Block1Chunk1RowCheck 7
    && tttLargeFiber72Block1Chunk1RowCheck 8
    && tttLargeFiber72Block1Chunk1RowCheck 9
    && tttLargeFiber72Block1Chunk1RowCheck 10
    && tttLargeFiber72Block1Chunk1RowCheck 11
    && tttLargeFiber72Block1Chunk1RowCheck 12
    && tttLargeFiber72Block1Chunk1RowCheck 13
    && tttLargeFiber72Block1Chunk1RowCheck 14
    && tttLargeFiber72Block1Chunk1RowCheck 15

theorem tttLargeFiber72Block1Chunk1RowsAudit_ok :
    tttLargeFiber72Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber72Block1Chunk1RowsAudit,
    tttLargeFiber72Block1Chunk1Row_0_ok,
    tttLargeFiber72Block1Chunk1Row_1_ok,
    tttLargeFiber72Block1Chunk1Row_2_ok,
    tttLargeFiber72Block1Chunk1Row_3_ok,
    tttLargeFiber72Block1Chunk1Row_4_ok,
    tttLargeFiber72Block1Chunk1Row_5_ok,
    tttLargeFiber72Block1Chunk1Row_6_ok,
    tttLargeFiber72Block1Chunk1Row_7_ok,
    tttLargeFiber72Block1Chunk1Row_8_ok,
    tttLargeFiber72Block1Chunk1Row_9_ok,
    tttLargeFiber72Block1Chunk1Row_10_ok,
    tttLargeFiber72Block1Chunk1Row_11_ok,
    tttLargeFiber72Block1Chunk1Row_12_ok,
    tttLargeFiber72Block1Chunk1Row_13_ok,
    tttLargeFiber72Block1Chunk1Row_14_ok,
    tttLargeFiber72Block1Chunk1Row_15_ok]

def tttLargeFiber72Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber72Block1Chunk1ParentMapCheck 0
    && tttLargeFiber72Block1Chunk1ParentMapCheck 1
    && tttLargeFiber72Block1Chunk1ParentMapCheck 2
    && tttLargeFiber72Block1Chunk1ParentMapCheck 3
    && tttLargeFiber72Block1Chunk1ParentMapCheck 4
    && tttLargeFiber72Block1Chunk1ParentMapCheck 5
    && tttLargeFiber72Block1Chunk1ParentMapCheck 6
    && tttLargeFiber72Block1Chunk1ParentMapCheck 7
    && tttLargeFiber72Block1Chunk1ParentMapCheck 8
    && tttLargeFiber72Block1Chunk1ParentMapCheck 9
    && tttLargeFiber72Block1Chunk1ParentMapCheck 10
    && tttLargeFiber72Block1Chunk1ParentMapCheck 11
    && tttLargeFiber72Block1Chunk1ParentMapCheck 12
    && tttLargeFiber72Block1Chunk1ParentMapCheck 13
    && tttLargeFiber72Block1Chunk1ParentMapCheck 14
    && tttLargeFiber72Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber72Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber72Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber72Block1Chunk1ParentMapAudit,
    tttLargeFiber72Block1Chunk1ParentMap_0_ok,
    tttLargeFiber72Block1Chunk1ParentMap_1_ok,
    tttLargeFiber72Block1Chunk1ParentMap_2_ok,
    tttLargeFiber72Block1Chunk1ParentMap_3_ok,
    tttLargeFiber72Block1Chunk1ParentMap_4_ok,
    tttLargeFiber72Block1Chunk1ParentMap_5_ok,
    tttLargeFiber72Block1Chunk1ParentMap_6_ok,
    tttLargeFiber72Block1Chunk1ParentMap_7_ok,
    tttLargeFiber72Block1Chunk1ParentMap_8_ok,
    tttLargeFiber72Block1Chunk1ParentMap_9_ok,
    tttLargeFiber72Block1Chunk1ParentMap_10_ok,
    tttLargeFiber72Block1Chunk1ParentMap_11_ok,
    tttLargeFiber72Block1Chunk1ParentMap_12_ok,
    tttLargeFiber72Block1Chunk1ParentMap_13_ok,
    tttLargeFiber72Block1Chunk1ParentMap_14_ok,
    tttLargeFiber72Block1Chunk1ParentMap_15_ok]

def tttLargeFiber72Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber72Block1Chunk1ParentPathCheck 0
    && tttLargeFiber72Block1Chunk1ParentPathCheck 1
    && tttLargeFiber72Block1Chunk1ParentPathCheck 2
    && tttLargeFiber72Block1Chunk1ParentPathCheck 3
    && tttLargeFiber72Block1Chunk1ParentPathCheck 4
    && tttLargeFiber72Block1Chunk1ParentPathCheck 5
    && tttLargeFiber72Block1Chunk1ParentPathCheck 6
    && tttLargeFiber72Block1Chunk1ParentPathCheck 7
    && tttLargeFiber72Block1Chunk1ParentPathCheck 8
    && tttLargeFiber72Block1Chunk1ParentPathCheck 9
    && tttLargeFiber72Block1Chunk1ParentPathCheck 10
    && tttLargeFiber72Block1Chunk1ParentPathCheck 11
    && tttLargeFiber72Block1Chunk1ParentPathCheck 12
    && tttLargeFiber72Block1Chunk1ParentPathCheck 13
    && tttLargeFiber72Block1Chunk1ParentPathCheck 14
    && tttLargeFiber72Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber72Block1Chunk1ParentsAudit_ok :
    tttLargeFiber72Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber72Block1Chunk1ParentsAudit,
    tttLargeFiber72Block1Chunk1ParentPath_0_ok,
    tttLargeFiber72Block1Chunk1ParentPath_1_ok,
    tttLargeFiber72Block1Chunk1ParentPath_2_ok,
    tttLargeFiber72Block1Chunk1ParentPath_3_ok,
    tttLargeFiber72Block1Chunk1ParentPath_4_ok,
    tttLargeFiber72Block1Chunk1ParentPath_5_ok,
    tttLargeFiber72Block1Chunk1ParentPath_6_ok,
    tttLargeFiber72Block1Chunk1ParentPath_7_ok,
    tttLargeFiber72Block1Chunk1ParentPath_8_ok,
    tttLargeFiber72Block1Chunk1ParentPath_9_ok,
    tttLargeFiber72Block1Chunk1ParentPath_10_ok,
    tttLargeFiber72Block1Chunk1ParentPath_11_ok,
    tttLargeFiber72Block1Chunk1ParentPath_12_ok,
    tttLargeFiber72Block1Chunk1ParentPath_13_ok,
    tttLargeFiber72Block1Chunk1ParentPath_14_ok,
    tttLargeFiber72Block1Chunk1ParentPath_15_ok]

def tttLargeFiber72Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block1Chunk1SourcesCheck &&
    tttLargeFiber72Block1Chunk1RowsAudit &&
    tttLargeFiber72Block1Chunk1ParentMapAudit &&
    tttLargeFiber72Block1Chunk1ParentsAudit

theorem tttLargeFiber72Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber72Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block1Chunk1SourcesCheck_ok,
    tttLargeFiber72Block1Chunk1RowsAudit_ok,
    tttLargeFiber72Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber72Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
