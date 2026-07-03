import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block1Chunk0Sources : List Nat :=
  [   2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791,
   2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]

def tttLargeFiber70Row64 : TripleComponentParentRow :=
  tripleRow 2784 2720 81 88 80 80 80 80
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row65 : TripleComponentParentRow :=
  tripleRow 2785 2721 81 88 81 80 80 81
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row66 : TripleComponentParentRow :=
  tripleRow 2786 2722 81 88 82 80 80 82
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row67 : TripleComponentParentRow :=
  tripleRow 2787 2723 81 88 83 80 80 83
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row68 : TripleComponentParentRow :=
  tripleRow 2788 2724 81 88 100 80 80 100
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row69 : TripleComponentParentRow :=
  tripleRow 2789 2725 81 88 101 80 80 101
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row70 : TripleComponentParentRow :=
  tripleRow 2790 2726 81 88 102 80 80 102
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row71 : TripleComponentParentRow :=
  tripleRow 2791 2727 81 88 103 80 80 103
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row72 : TripleComponentParentRow :=
  tripleRow 2792 2728 81 89 88 80 81 88
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row73 : TripleComponentParentRow :=
  tripleRow 2793 2729 81 89 89 80 81 89
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row74 : TripleComponentParentRow :=
  tripleRow 2794 2730 81 89 90 80 81 90
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row75 : TripleComponentParentRow :=
  tripleRow 2795 2731 81 89 91 80 81 91
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row76 : TripleComponentParentRow :=
  tripleRow 2796 2732 81 89 108 80 81 108
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row77 : TripleComponentParentRow :=
  tripleRow 2797 2733 81 89 109 80 81 109
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row78 : TripleComponentParentRow :=
  tripleRow 2798 2734 81 89 110 80 81 110
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row79 : TripleComponentParentRow :=
  tripleRow 2799 2735 81 89 111 80 81 111
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row64
  , tttLargeFiber70Row65
  , tttLargeFiber70Row66
  , tttLargeFiber70Row67
  , tttLargeFiber70Row68
  , tttLargeFiber70Row69
  , tttLargeFiber70Row70
  , tttLargeFiber70Row71
  , tttLargeFiber70Row72
  , tttLargeFiber70Row73
  , tttLargeFiber70Row74
  , tttLargeFiber70Row75
  , tttLargeFiber70Row76
  , tttLargeFiber70Row77
  , tttLargeFiber70Row78
  , tttLargeFiber70Row79
  ]

def tttLargeFiber70Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber70Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber70Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber70Block1Chunk0Sources

theorem tttLargeFiber70Block1Chunk0SourcesCheck_ok :
    tttLargeFiber70Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber70Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block1Chunk0RowValid
    (listGetD tttLargeFiber70Block1Chunk0Rows i default)

def tttLargeFiber70Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block1Chunk0Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block1Chunk0Sources 0 0 == 2784
      && tttLargeFiber70ParentOf 2784 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (1 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block1Chunk0Sources 1 0 == 2785
      && tttLargeFiber70ParentOf 2785 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block1Chunk0Sources 2 0 == 2786
      && tttLargeFiber70ParentOf 2786 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block1Chunk0Sources 3 0 == 2787
      && tttLargeFiber70ParentOf 2787 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block1Chunk0Sources 4 0 == 2788
      && tttLargeFiber70ParentOf 2788 == 2724
      && tttLargeFiber70ParentOf 2724 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block1Chunk0Sources 5 0 == 2789
      && tttLargeFiber70ParentOf 2789 == 2725
      && tttLargeFiber70ParentOf 2725 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block1Chunk0Sources 6 0 == 2790
      && tttLargeFiber70ParentOf 2790 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block1Chunk0Sources 7 0 == 2791
      && tttLargeFiber70ParentOf 2791 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block1Chunk0Sources 8 0 == 2792
      && tttLargeFiber70ParentOf 2792 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block1Chunk0Sources 9 0 == 2793
      && tttLargeFiber70ParentOf 2793 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block1Chunk0Sources 10 0 == 2794
      && tttLargeFiber70ParentOf 2794 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block1Chunk0Sources 11 0 == 2795
      && tttLargeFiber70ParentOf 2795 == 2731
      && tttLargeFiber70ParentOf 2731 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block1Chunk0Sources 12 0 == 2796
      && tttLargeFiber70ParentOf 2796 == 2732
      && tttLargeFiber70ParentOf 2732 == 2724
      && tttLargeFiber70ParentOf 2724 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block1Chunk0Sources 13 0 == 2797
      && tttLargeFiber70ParentOf 2797 == 2733
      && tttLargeFiber70ParentOf 2733 == 2725
      && tttLargeFiber70ParentOf 2725 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block1Chunk0Sources 14 0 == 2798
      && tttLargeFiber70ParentOf 2798 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block1Chunk0Sources 15 0 == 2799
      && tttLargeFiber70ParentOf 2799 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block1Chunk0Row_0_ok :
    tttLargeFiber70Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_1_ok :
    tttLargeFiber70Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_2_ok :
    tttLargeFiber70Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_3_ok :
    tttLargeFiber70Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_4_ok :
    tttLargeFiber70Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_5_ok :
    tttLargeFiber70Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_6_ok :
    tttLargeFiber70Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_7_ok :
    tttLargeFiber70Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_8_ok :
    tttLargeFiber70Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_9_ok :
    tttLargeFiber70Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_10_ok :
    tttLargeFiber70Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_11_ok :
    tttLargeFiber70Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_12_ok :
    tttLargeFiber70Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_13_ok :
    tttLargeFiber70Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_14_ok :
    tttLargeFiber70Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0Row_15_ok :
    tttLargeFiber70Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_0_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_1_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_2_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_3_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_4_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_5_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_6_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_7_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_8_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_9_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_10_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_11_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_12_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_13_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_14_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentMap_15_ok :
    tttLargeFiber70Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_0_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_1_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_2_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_3_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_4_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_5_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_6_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_7_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_8_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_9_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_10_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_11_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_12_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_13_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_14_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk0ParentPath_15_ok :
    tttLargeFiber70Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber70Block1Chunk0RowCheck 0
    && tttLargeFiber70Block1Chunk0RowCheck 1
    && tttLargeFiber70Block1Chunk0RowCheck 2
    && tttLargeFiber70Block1Chunk0RowCheck 3
    && tttLargeFiber70Block1Chunk0RowCheck 4
    && tttLargeFiber70Block1Chunk0RowCheck 5
    && tttLargeFiber70Block1Chunk0RowCheck 6
    && tttLargeFiber70Block1Chunk0RowCheck 7
    && tttLargeFiber70Block1Chunk0RowCheck 8
    && tttLargeFiber70Block1Chunk0RowCheck 9
    && tttLargeFiber70Block1Chunk0RowCheck 10
    && tttLargeFiber70Block1Chunk0RowCheck 11
    && tttLargeFiber70Block1Chunk0RowCheck 12
    && tttLargeFiber70Block1Chunk0RowCheck 13
    && tttLargeFiber70Block1Chunk0RowCheck 14
    && tttLargeFiber70Block1Chunk0RowCheck 15

theorem tttLargeFiber70Block1Chunk0RowsAudit_ok :
    tttLargeFiber70Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber70Block1Chunk0RowsAudit,
    tttLargeFiber70Block1Chunk0Row_0_ok,
    tttLargeFiber70Block1Chunk0Row_1_ok,
    tttLargeFiber70Block1Chunk0Row_2_ok,
    tttLargeFiber70Block1Chunk0Row_3_ok,
    tttLargeFiber70Block1Chunk0Row_4_ok,
    tttLargeFiber70Block1Chunk0Row_5_ok,
    tttLargeFiber70Block1Chunk0Row_6_ok,
    tttLargeFiber70Block1Chunk0Row_7_ok,
    tttLargeFiber70Block1Chunk0Row_8_ok,
    tttLargeFiber70Block1Chunk0Row_9_ok,
    tttLargeFiber70Block1Chunk0Row_10_ok,
    tttLargeFiber70Block1Chunk0Row_11_ok,
    tttLargeFiber70Block1Chunk0Row_12_ok,
    tttLargeFiber70Block1Chunk0Row_13_ok,
    tttLargeFiber70Block1Chunk0Row_14_ok,
    tttLargeFiber70Block1Chunk0Row_15_ok]

def tttLargeFiber70Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber70Block1Chunk0ParentMapCheck 0
    && tttLargeFiber70Block1Chunk0ParentMapCheck 1
    && tttLargeFiber70Block1Chunk0ParentMapCheck 2
    && tttLargeFiber70Block1Chunk0ParentMapCheck 3
    && tttLargeFiber70Block1Chunk0ParentMapCheck 4
    && tttLargeFiber70Block1Chunk0ParentMapCheck 5
    && tttLargeFiber70Block1Chunk0ParentMapCheck 6
    && tttLargeFiber70Block1Chunk0ParentMapCheck 7
    && tttLargeFiber70Block1Chunk0ParentMapCheck 8
    && tttLargeFiber70Block1Chunk0ParentMapCheck 9
    && tttLargeFiber70Block1Chunk0ParentMapCheck 10
    && tttLargeFiber70Block1Chunk0ParentMapCheck 11
    && tttLargeFiber70Block1Chunk0ParentMapCheck 12
    && tttLargeFiber70Block1Chunk0ParentMapCheck 13
    && tttLargeFiber70Block1Chunk0ParentMapCheck 14
    && tttLargeFiber70Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber70Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber70Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber70Block1Chunk0ParentMapAudit,
    tttLargeFiber70Block1Chunk0ParentMap_0_ok,
    tttLargeFiber70Block1Chunk0ParentMap_1_ok,
    tttLargeFiber70Block1Chunk0ParentMap_2_ok,
    tttLargeFiber70Block1Chunk0ParentMap_3_ok,
    tttLargeFiber70Block1Chunk0ParentMap_4_ok,
    tttLargeFiber70Block1Chunk0ParentMap_5_ok,
    tttLargeFiber70Block1Chunk0ParentMap_6_ok,
    tttLargeFiber70Block1Chunk0ParentMap_7_ok,
    tttLargeFiber70Block1Chunk0ParentMap_8_ok,
    tttLargeFiber70Block1Chunk0ParentMap_9_ok,
    tttLargeFiber70Block1Chunk0ParentMap_10_ok,
    tttLargeFiber70Block1Chunk0ParentMap_11_ok,
    tttLargeFiber70Block1Chunk0ParentMap_12_ok,
    tttLargeFiber70Block1Chunk0ParentMap_13_ok,
    tttLargeFiber70Block1Chunk0ParentMap_14_ok,
    tttLargeFiber70Block1Chunk0ParentMap_15_ok]

def tttLargeFiber70Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber70Block1Chunk0ParentPathCheck 0
    && tttLargeFiber70Block1Chunk0ParentPathCheck 1
    && tttLargeFiber70Block1Chunk0ParentPathCheck 2
    && tttLargeFiber70Block1Chunk0ParentPathCheck 3
    && tttLargeFiber70Block1Chunk0ParentPathCheck 4
    && tttLargeFiber70Block1Chunk0ParentPathCheck 5
    && tttLargeFiber70Block1Chunk0ParentPathCheck 6
    && tttLargeFiber70Block1Chunk0ParentPathCheck 7
    && tttLargeFiber70Block1Chunk0ParentPathCheck 8
    && tttLargeFiber70Block1Chunk0ParentPathCheck 9
    && tttLargeFiber70Block1Chunk0ParentPathCheck 10
    && tttLargeFiber70Block1Chunk0ParentPathCheck 11
    && tttLargeFiber70Block1Chunk0ParentPathCheck 12
    && tttLargeFiber70Block1Chunk0ParentPathCheck 13
    && tttLargeFiber70Block1Chunk0ParentPathCheck 14
    && tttLargeFiber70Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber70Block1Chunk0ParentsAudit_ok :
    tttLargeFiber70Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber70Block1Chunk0ParentsAudit,
    tttLargeFiber70Block1Chunk0ParentPath_0_ok,
    tttLargeFiber70Block1Chunk0ParentPath_1_ok,
    tttLargeFiber70Block1Chunk0ParentPath_2_ok,
    tttLargeFiber70Block1Chunk0ParentPath_3_ok,
    tttLargeFiber70Block1Chunk0ParentPath_4_ok,
    tttLargeFiber70Block1Chunk0ParentPath_5_ok,
    tttLargeFiber70Block1Chunk0ParentPath_6_ok,
    tttLargeFiber70Block1Chunk0ParentPath_7_ok,
    tttLargeFiber70Block1Chunk0ParentPath_8_ok,
    tttLargeFiber70Block1Chunk0ParentPath_9_ok,
    tttLargeFiber70Block1Chunk0ParentPath_10_ok,
    tttLargeFiber70Block1Chunk0ParentPath_11_ok,
    tttLargeFiber70Block1Chunk0ParentPath_12_ok,
    tttLargeFiber70Block1Chunk0ParentPath_13_ok,
    tttLargeFiber70Block1Chunk0ParentPath_14_ok,
    tttLargeFiber70Block1Chunk0ParentPath_15_ok]

def tttLargeFiber70Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block1Chunk0SourcesCheck &&
    tttLargeFiber70Block1Chunk0RowsAudit &&
    tttLargeFiber70Block1Chunk0ParentMapAudit &&
    tttLargeFiber70Block1Chunk0ParentsAudit

theorem tttLargeFiber70Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber70Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block1Chunk0SourcesCheck_ok,
    tttLargeFiber70Block1Chunk0RowsAudit_ok,
    tttLargeFiber70Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber70Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
