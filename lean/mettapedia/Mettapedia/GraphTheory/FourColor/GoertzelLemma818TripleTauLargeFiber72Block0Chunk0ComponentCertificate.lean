import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block0Chunk0Sources : List Nat :=
  [   816, 817, 818, 819, 820, 821, 822, 823,
   824, 825, 826, 827, 828, 829, 830, 831]

def tttLargeFiber72Row0 : TripleComponentParentRow :=
  tripleRow 816 816 24 80 80 24 80 80
    default
    []

def tttLargeFiber72Row1 : TripleComponentParentRow :=
  tripleRow 817 816 24 80 81 24 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row2 : TripleComponentParentRow :=
  tripleRow 818 816 24 80 82 24 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row3 : TripleComponentParentRow :=
  tripleRow 819 817 24 80 83 24 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row4 : TripleComponentParentRow :=
  tripleRow 820 818 24 80 100 24 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row5 : TripleComponentParentRow :=
  tripleRow 821 823 24 80 101 24 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row6 : TripleComponentParentRow :=
  tripleRow 822 817 24 80 102 24 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row7 : TripleComponentParentRow :=
  tripleRow 823 816 24 80 103 24 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row8 : TripleComponentParentRow :=
  tripleRow 824 816 24 81 88 24 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Row9 : TripleComponentParentRow :=
  tripleRow 825 817 24 81 89 24 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Row10 : TripleComponentParentRow :=
  tripleRow 826 818 24 81 90 24 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Row11 : TripleComponentParentRow :=
  tripleRow 827 819 24 81 91 24 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Row12 : TripleComponentParentRow :=
  tripleRow 828 820 24 81 108 24 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Row13 : TripleComponentParentRow :=
  tripleRow 829 821 24 81 109 24 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Row14 : TripleComponentParentRow :=
  tripleRow 830 822 24 81 110 24 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Row15 : TripleComponentParentRow :=
  tripleRow 831 823 24 81 111 24 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber72Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row0
  , tttLargeFiber72Row1
  , tttLargeFiber72Row2
  , tttLargeFiber72Row3
  , tttLargeFiber72Row4
  , tttLargeFiber72Row5
  , tttLargeFiber72Row6
  , tttLargeFiber72Row7
  , tttLargeFiber72Row8
  , tttLargeFiber72Row9
  , tttLargeFiber72Row10
  , tttLargeFiber72Row11
  , tttLargeFiber72Row12
  , tttLargeFiber72Row13
  , tttLargeFiber72Row14
  , tttLargeFiber72Row15
  ]

def tttLargeFiber72Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber72Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber72Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber72Block0Chunk0Sources

theorem tttLargeFiber72Block0Chunk0SourcesCheck_ok :
    tttLargeFiber72Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber72Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block0Chunk0RowValid
    (listGetD tttLargeFiber72Block0Chunk0Rows i default)

def tttLargeFiber72Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block0Chunk0Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block0Chunk0Sources 0 0 == 816
      && 816 == tttLargeFiber72Root
      && decide (0 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block0Chunk0Sources 1 0 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (1 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block0Chunk0Sources 2 0 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (1 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block0Chunk0Sources 3 0 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block0Chunk0Sources 4 0 == 820
      && tttLargeFiber72ParentOf 820 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block0Chunk0Sources 5 0 == 821
      && tttLargeFiber72ParentOf 821 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block0Chunk0Sources 6 0 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block0Chunk0Sources 7 0 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (1 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block0Chunk0Sources 8 0 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (1 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block0Chunk0Sources 9 0 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block0Chunk0Sources 10 0 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block0Chunk0Sources 11 0 == 827
      && tttLargeFiber72ParentOf 827 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block0Chunk0Sources 12 0 == 828
      && tttLargeFiber72ParentOf 828 == 820
      && tttLargeFiber72ParentOf 820 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block0Chunk0Sources 13 0 == 829
      && tttLargeFiber72ParentOf 829 == 821
      && tttLargeFiber72ParentOf 821 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block0Chunk0Sources 14 0 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block0Chunk0Sources 15 0 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block0Chunk0Row_0_ok :
    tttLargeFiber72Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_1_ok :
    tttLargeFiber72Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_2_ok :
    tttLargeFiber72Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_3_ok :
    tttLargeFiber72Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_4_ok :
    tttLargeFiber72Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_5_ok :
    tttLargeFiber72Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_6_ok :
    tttLargeFiber72Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_7_ok :
    tttLargeFiber72Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_8_ok :
    tttLargeFiber72Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_9_ok :
    tttLargeFiber72Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_10_ok :
    tttLargeFiber72Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_11_ok :
    tttLargeFiber72Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_12_ok :
    tttLargeFiber72Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_13_ok :
    tttLargeFiber72Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_14_ok :
    tttLargeFiber72Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0Row_15_ok :
    tttLargeFiber72Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_0_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_1_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_2_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_3_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_4_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_5_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_6_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_7_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_8_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_9_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_10_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_11_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_12_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_13_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_14_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentMap_15_ok :
    tttLargeFiber72Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_0_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_1_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_2_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_3_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_4_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_5_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_6_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_7_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_8_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_9_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_10_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_11_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_12_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_13_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_14_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk0ParentPath_15_ok :
    tttLargeFiber72Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber72Block0Chunk0RowCheck 0
    && tttLargeFiber72Block0Chunk0RowCheck 1
    && tttLargeFiber72Block0Chunk0RowCheck 2
    && tttLargeFiber72Block0Chunk0RowCheck 3
    && tttLargeFiber72Block0Chunk0RowCheck 4
    && tttLargeFiber72Block0Chunk0RowCheck 5
    && tttLargeFiber72Block0Chunk0RowCheck 6
    && tttLargeFiber72Block0Chunk0RowCheck 7
    && tttLargeFiber72Block0Chunk0RowCheck 8
    && tttLargeFiber72Block0Chunk0RowCheck 9
    && tttLargeFiber72Block0Chunk0RowCheck 10
    && tttLargeFiber72Block0Chunk0RowCheck 11
    && tttLargeFiber72Block0Chunk0RowCheck 12
    && tttLargeFiber72Block0Chunk0RowCheck 13
    && tttLargeFiber72Block0Chunk0RowCheck 14
    && tttLargeFiber72Block0Chunk0RowCheck 15

theorem tttLargeFiber72Block0Chunk0RowsAudit_ok :
    tttLargeFiber72Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber72Block0Chunk0RowsAudit,
    tttLargeFiber72Block0Chunk0Row_0_ok,
    tttLargeFiber72Block0Chunk0Row_1_ok,
    tttLargeFiber72Block0Chunk0Row_2_ok,
    tttLargeFiber72Block0Chunk0Row_3_ok,
    tttLargeFiber72Block0Chunk0Row_4_ok,
    tttLargeFiber72Block0Chunk0Row_5_ok,
    tttLargeFiber72Block0Chunk0Row_6_ok,
    tttLargeFiber72Block0Chunk0Row_7_ok,
    tttLargeFiber72Block0Chunk0Row_8_ok,
    tttLargeFiber72Block0Chunk0Row_9_ok,
    tttLargeFiber72Block0Chunk0Row_10_ok,
    tttLargeFiber72Block0Chunk0Row_11_ok,
    tttLargeFiber72Block0Chunk0Row_12_ok,
    tttLargeFiber72Block0Chunk0Row_13_ok,
    tttLargeFiber72Block0Chunk0Row_14_ok,
    tttLargeFiber72Block0Chunk0Row_15_ok]

def tttLargeFiber72Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber72Block0Chunk0ParentMapCheck 0
    && tttLargeFiber72Block0Chunk0ParentMapCheck 1
    && tttLargeFiber72Block0Chunk0ParentMapCheck 2
    && tttLargeFiber72Block0Chunk0ParentMapCheck 3
    && tttLargeFiber72Block0Chunk0ParentMapCheck 4
    && tttLargeFiber72Block0Chunk0ParentMapCheck 5
    && tttLargeFiber72Block0Chunk0ParentMapCheck 6
    && tttLargeFiber72Block0Chunk0ParentMapCheck 7
    && tttLargeFiber72Block0Chunk0ParentMapCheck 8
    && tttLargeFiber72Block0Chunk0ParentMapCheck 9
    && tttLargeFiber72Block0Chunk0ParentMapCheck 10
    && tttLargeFiber72Block0Chunk0ParentMapCheck 11
    && tttLargeFiber72Block0Chunk0ParentMapCheck 12
    && tttLargeFiber72Block0Chunk0ParentMapCheck 13
    && tttLargeFiber72Block0Chunk0ParentMapCheck 14
    && tttLargeFiber72Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber72Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber72Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber72Block0Chunk0ParentMapAudit,
    tttLargeFiber72Block0Chunk0ParentMap_0_ok,
    tttLargeFiber72Block0Chunk0ParentMap_1_ok,
    tttLargeFiber72Block0Chunk0ParentMap_2_ok,
    tttLargeFiber72Block0Chunk0ParentMap_3_ok,
    tttLargeFiber72Block0Chunk0ParentMap_4_ok,
    tttLargeFiber72Block0Chunk0ParentMap_5_ok,
    tttLargeFiber72Block0Chunk0ParentMap_6_ok,
    tttLargeFiber72Block0Chunk0ParentMap_7_ok,
    tttLargeFiber72Block0Chunk0ParentMap_8_ok,
    tttLargeFiber72Block0Chunk0ParentMap_9_ok,
    tttLargeFiber72Block0Chunk0ParentMap_10_ok,
    tttLargeFiber72Block0Chunk0ParentMap_11_ok,
    tttLargeFiber72Block0Chunk0ParentMap_12_ok,
    tttLargeFiber72Block0Chunk0ParentMap_13_ok,
    tttLargeFiber72Block0Chunk0ParentMap_14_ok,
    tttLargeFiber72Block0Chunk0ParentMap_15_ok]

def tttLargeFiber72Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber72Block0Chunk0ParentPathCheck 0
    && tttLargeFiber72Block0Chunk0ParentPathCheck 1
    && tttLargeFiber72Block0Chunk0ParentPathCheck 2
    && tttLargeFiber72Block0Chunk0ParentPathCheck 3
    && tttLargeFiber72Block0Chunk0ParentPathCheck 4
    && tttLargeFiber72Block0Chunk0ParentPathCheck 5
    && tttLargeFiber72Block0Chunk0ParentPathCheck 6
    && tttLargeFiber72Block0Chunk0ParentPathCheck 7
    && tttLargeFiber72Block0Chunk0ParentPathCheck 8
    && tttLargeFiber72Block0Chunk0ParentPathCheck 9
    && tttLargeFiber72Block0Chunk0ParentPathCheck 10
    && tttLargeFiber72Block0Chunk0ParentPathCheck 11
    && tttLargeFiber72Block0Chunk0ParentPathCheck 12
    && tttLargeFiber72Block0Chunk0ParentPathCheck 13
    && tttLargeFiber72Block0Chunk0ParentPathCheck 14
    && tttLargeFiber72Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber72Block0Chunk0ParentsAudit_ok :
    tttLargeFiber72Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber72Block0Chunk0ParentsAudit,
    tttLargeFiber72Block0Chunk0ParentPath_0_ok,
    tttLargeFiber72Block0Chunk0ParentPath_1_ok,
    tttLargeFiber72Block0Chunk0ParentPath_2_ok,
    tttLargeFiber72Block0Chunk0ParentPath_3_ok,
    tttLargeFiber72Block0Chunk0ParentPath_4_ok,
    tttLargeFiber72Block0Chunk0ParentPath_5_ok,
    tttLargeFiber72Block0Chunk0ParentPath_6_ok,
    tttLargeFiber72Block0Chunk0ParentPath_7_ok,
    tttLargeFiber72Block0Chunk0ParentPath_8_ok,
    tttLargeFiber72Block0Chunk0ParentPath_9_ok,
    tttLargeFiber72Block0Chunk0ParentPath_10_ok,
    tttLargeFiber72Block0Chunk0ParentPath_11_ok,
    tttLargeFiber72Block0Chunk0ParentPath_12_ok,
    tttLargeFiber72Block0Chunk0ParentPath_13_ok,
    tttLargeFiber72Block0Chunk0ParentPath_14_ok,
    tttLargeFiber72Block0Chunk0ParentPath_15_ok]

def tttLargeFiber72Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block0Chunk0SourcesCheck &&
    tttLargeFiber72Block0Chunk0RowsAudit &&
    tttLargeFiber72Block0Chunk0ParentMapAudit &&
    tttLargeFiber72Block0Chunk0ParentsAudit

theorem tttLargeFiber72Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber72Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block0Chunk0SourcesCheck_ok,
    tttLargeFiber72Block0Chunk0RowsAudit_ok,
    tttLargeFiber72Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber72Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
