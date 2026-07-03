import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block1Chunk1Sources : List Nat :=
  [   2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807,
   2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]

def tttLargeFiber70Row80 : TripleComponentParentRow :=
  tripleRow 2800 2736 81 90 16 80 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row81 : TripleComponentParentRow :=
  tripleRow 2801 2737 81 90 17 80 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row82 : TripleComponentParentRow :=
  tripleRow 2802 2738 81 90 18 80 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row83 : TripleComponentParentRow :=
  tripleRow 2803 2739 81 90 19 80 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row84 : TripleComponentParentRow :=
  tripleRow 2804 2740 81 90 32 80 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row85 : TripleComponentParentRow :=
  tripleRow 2805 2741 81 90 33 80 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row86 : TripleComponentParentRow :=
  tripleRow 2806 2742 81 90 34 80 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row87 : TripleComponentParentRow :=
  tripleRow 2807 2743 81 90 35 80 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row88 : TripleComponentParentRow :=
  tripleRow 2808 2744 81 91 24 80 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row89 : TripleComponentParentRow :=
  tripleRow 2809 2745 81 91 25 80 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row90 : TripleComponentParentRow :=
  tripleRow 2810 2746 81 91 26 80 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row91 : TripleComponentParentRow :=
  tripleRow 2811 2747 81 91 27 80 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row92 : TripleComponentParentRow :=
  tripleRow 2812 2748 81 91 40 80 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row93 : TripleComponentParentRow :=
  tripleRow 2813 2749 81 91 41 80 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row94 : TripleComponentParentRow :=
  tripleRow 2814 2750 81 91 42 80 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row95 : TripleComponentParentRow :=
  tripleRow 2815 2751 81 91 43 80 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row80
  , tttLargeFiber70Row81
  , tttLargeFiber70Row82
  , tttLargeFiber70Row83
  , tttLargeFiber70Row84
  , tttLargeFiber70Row85
  , tttLargeFiber70Row86
  , tttLargeFiber70Row87
  , tttLargeFiber70Row88
  , tttLargeFiber70Row89
  , tttLargeFiber70Row90
  , tttLargeFiber70Row91
  , tttLargeFiber70Row92
  , tttLargeFiber70Row93
  , tttLargeFiber70Row94
  , tttLargeFiber70Row95
  ]

def tttLargeFiber70Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber70Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber70Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber70Block1Chunk1Sources

theorem tttLargeFiber70Block1Chunk1SourcesCheck_ok :
    tttLargeFiber70Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber70Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block1Chunk1RowValid
    (listGetD tttLargeFiber70Block1Chunk1Rows i default)

def tttLargeFiber70Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block1Chunk1Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block1Chunk1Sources 0 0 == 2800
      && tttLargeFiber70ParentOf 2800 == 2736
      && tttLargeFiber70ParentOf 2736 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block1Chunk1Sources 1 0 == 2801
      && tttLargeFiber70ParentOf 2801 == 2737
      && tttLargeFiber70ParentOf 2737 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block1Chunk1Sources 2 0 == 2802
      && tttLargeFiber70ParentOf 2802 == 2738
      && tttLargeFiber70ParentOf 2738 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block1Chunk1Sources 3 0 == 2803
      && tttLargeFiber70ParentOf 2803 == 2739
      && tttLargeFiber70ParentOf 2739 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block1Chunk1Sources 4 0 == 2804
      && tttLargeFiber70ParentOf 2804 == 2740
      && tttLargeFiber70ParentOf 2740 == 2736
      && tttLargeFiber70ParentOf 2736 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block1Chunk1Sources 5 0 == 2805
      && tttLargeFiber70ParentOf 2805 == 2741
      && tttLargeFiber70ParentOf 2741 == 2737
      && tttLargeFiber70ParentOf 2737 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block1Chunk1Sources 6 0 == 2806
      && tttLargeFiber70ParentOf 2806 == 2742
      && tttLargeFiber70ParentOf 2742 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block1Chunk1Sources 7 0 == 2807
      && tttLargeFiber70ParentOf 2807 == 2743
      && tttLargeFiber70ParentOf 2743 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block1Chunk1Sources 8 0 == 2808
      && tttLargeFiber70ParentOf 2808 == 2744
      && tttLargeFiber70ParentOf 2744 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block1Chunk1Sources 9 0 == 2809
      && tttLargeFiber70ParentOf 2809 == 2745
      && tttLargeFiber70ParentOf 2745 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block1Chunk1Sources 10 0 == 2810
      && tttLargeFiber70ParentOf 2810 == 2746
      && tttLargeFiber70ParentOf 2746 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block1Chunk1Sources 11 0 == 2811
      && tttLargeFiber70ParentOf 2811 == 2747
      && tttLargeFiber70ParentOf 2747 == 2731
      && tttLargeFiber70ParentOf 2731 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block1Chunk1Sources 12 0 == 2812
      && tttLargeFiber70ParentOf 2812 == 2748
      && tttLargeFiber70ParentOf 2748 == 2744
      && tttLargeFiber70ParentOf 2744 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block1Chunk1Sources 13 0 == 2813
      && tttLargeFiber70ParentOf 2813 == 2749
      && tttLargeFiber70ParentOf 2749 == 2745
      && tttLargeFiber70ParentOf 2745 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block1Chunk1Sources 14 0 == 2814
      && tttLargeFiber70ParentOf 2814 == 2750
      && tttLargeFiber70ParentOf 2750 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block1Chunk1Sources 15 0 == 2815
      && tttLargeFiber70ParentOf 2815 == 2751
      && tttLargeFiber70ParentOf 2751 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block1Chunk1Row_0_ok :
    tttLargeFiber70Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_1_ok :
    tttLargeFiber70Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_2_ok :
    tttLargeFiber70Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_3_ok :
    tttLargeFiber70Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_4_ok :
    tttLargeFiber70Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_5_ok :
    tttLargeFiber70Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_6_ok :
    tttLargeFiber70Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_7_ok :
    tttLargeFiber70Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_8_ok :
    tttLargeFiber70Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_9_ok :
    tttLargeFiber70Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_10_ok :
    tttLargeFiber70Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_11_ok :
    tttLargeFiber70Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_12_ok :
    tttLargeFiber70Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_13_ok :
    tttLargeFiber70Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_14_ok :
    tttLargeFiber70Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1Row_15_ok :
    tttLargeFiber70Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_0_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_1_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_2_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_3_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_4_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_5_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_6_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_7_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_8_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_9_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_10_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_11_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_12_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_13_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_14_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentMap_15_ok :
    tttLargeFiber70Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_0_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_1_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_2_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_3_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_4_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_5_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_6_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_7_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_8_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_9_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_10_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_11_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_12_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_13_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_14_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk1ParentPath_15_ok :
    tttLargeFiber70Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber70Block1Chunk1RowCheck 0
    && tttLargeFiber70Block1Chunk1RowCheck 1
    && tttLargeFiber70Block1Chunk1RowCheck 2
    && tttLargeFiber70Block1Chunk1RowCheck 3
    && tttLargeFiber70Block1Chunk1RowCheck 4
    && tttLargeFiber70Block1Chunk1RowCheck 5
    && tttLargeFiber70Block1Chunk1RowCheck 6
    && tttLargeFiber70Block1Chunk1RowCheck 7
    && tttLargeFiber70Block1Chunk1RowCheck 8
    && tttLargeFiber70Block1Chunk1RowCheck 9
    && tttLargeFiber70Block1Chunk1RowCheck 10
    && tttLargeFiber70Block1Chunk1RowCheck 11
    && tttLargeFiber70Block1Chunk1RowCheck 12
    && tttLargeFiber70Block1Chunk1RowCheck 13
    && tttLargeFiber70Block1Chunk1RowCheck 14
    && tttLargeFiber70Block1Chunk1RowCheck 15

theorem tttLargeFiber70Block1Chunk1RowsAudit_ok :
    tttLargeFiber70Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber70Block1Chunk1RowsAudit,
    tttLargeFiber70Block1Chunk1Row_0_ok,
    tttLargeFiber70Block1Chunk1Row_1_ok,
    tttLargeFiber70Block1Chunk1Row_2_ok,
    tttLargeFiber70Block1Chunk1Row_3_ok,
    tttLargeFiber70Block1Chunk1Row_4_ok,
    tttLargeFiber70Block1Chunk1Row_5_ok,
    tttLargeFiber70Block1Chunk1Row_6_ok,
    tttLargeFiber70Block1Chunk1Row_7_ok,
    tttLargeFiber70Block1Chunk1Row_8_ok,
    tttLargeFiber70Block1Chunk1Row_9_ok,
    tttLargeFiber70Block1Chunk1Row_10_ok,
    tttLargeFiber70Block1Chunk1Row_11_ok,
    tttLargeFiber70Block1Chunk1Row_12_ok,
    tttLargeFiber70Block1Chunk1Row_13_ok,
    tttLargeFiber70Block1Chunk1Row_14_ok,
    tttLargeFiber70Block1Chunk1Row_15_ok]

def tttLargeFiber70Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber70Block1Chunk1ParentMapCheck 0
    && tttLargeFiber70Block1Chunk1ParentMapCheck 1
    && tttLargeFiber70Block1Chunk1ParentMapCheck 2
    && tttLargeFiber70Block1Chunk1ParentMapCheck 3
    && tttLargeFiber70Block1Chunk1ParentMapCheck 4
    && tttLargeFiber70Block1Chunk1ParentMapCheck 5
    && tttLargeFiber70Block1Chunk1ParentMapCheck 6
    && tttLargeFiber70Block1Chunk1ParentMapCheck 7
    && tttLargeFiber70Block1Chunk1ParentMapCheck 8
    && tttLargeFiber70Block1Chunk1ParentMapCheck 9
    && tttLargeFiber70Block1Chunk1ParentMapCheck 10
    && tttLargeFiber70Block1Chunk1ParentMapCheck 11
    && tttLargeFiber70Block1Chunk1ParentMapCheck 12
    && tttLargeFiber70Block1Chunk1ParentMapCheck 13
    && tttLargeFiber70Block1Chunk1ParentMapCheck 14
    && tttLargeFiber70Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber70Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber70Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber70Block1Chunk1ParentMapAudit,
    tttLargeFiber70Block1Chunk1ParentMap_0_ok,
    tttLargeFiber70Block1Chunk1ParentMap_1_ok,
    tttLargeFiber70Block1Chunk1ParentMap_2_ok,
    tttLargeFiber70Block1Chunk1ParentMap_3_ok,
    tttLargeFiber70Block1Chunk1ParentMap_4_ok,
    tttLargeFiber70Block1Chunk1ParentMap_5_ok,
    tttLargeFiber70Block1Chunk1ParentMap_6_ok,
    tttLargeFiber70Block1Chunk1ParentMap_7_ok,
    tttLargeFiber70Block1Chunk1ParentMap_8_ok,
    tttLargeFiber70Block1Chunk1ParentMap_9_ok,
    tttLargeFiber70Block1Chunk1ParentMap_10_ok,
    tttLargeFiber70Block1Chunk1ParentMap_11_ok,
    tttLargeFiber70Block1Chunk1ParentMap_12_ok,
    tttLargeFiber70Block1Chunk1ParentMap_13_ok,
    tttLargeFiber70Block1Chunk1ParentMap_14_ok,
    tttLargeFiber70Block1Chunk1ParentMap_15_ok]

def tttLargeFiber70Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber70Block1Chunk1ParentPathCheck 0
    && tttLargeFiber70Block1Chunk1ParentPathCheck 1
    && tttLargeFiber70Block1Chunk1ParentPathCheck 2
    && tttLargeFiber70Block1Chunk1ParentPathCheck 3
    && tttLargeFiber70Block1Chunk1ParentPathCheck 4
    && tttLargeFiber70Block1Chunk1ParentPathCheck 5
    && tttLargeFiber70Block1Chunk1ParentPathCheck 6
    && tttLargeFiber70Block1Chunk1ParentPathCheck 7
    && tttLargeFiber70Block1Chunk1ParentPathCheck 8
    && tttLargeFiber70Block1Chunk1ParentPathCheck 9
    && tttLargeFiber70Block1Chunk1ParentPathCheck 10
    && tttLargeFiber70Block1Chunk1ParentPathCheck 11
    && tttLargeFiber70Block1Chunk1ParentPathCheck 12
    && tttLargeFiber70Block1Chunk1ParentPathCheck 13
    && tttLargeFiber70Block1Chunk1ParentPathCheck 14
    && tttLargeFiber70Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber70Block1Chunk1ParentsAudit_ok :
    tttLargeFiber70Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber70Block1Chunk1ParentsAudit,
    tttLargeFiber70Block1Chunk1ParentPath_0_ok,
    tttLargeFiber70Block1Chunk1ParentPath_1_ok,
    tttLargeFiber70Block1Chunk1ParentPath_2_ok,
    tttLargeFiber70Block1Chunk1ParentPath_3_ok,
    tttLargeFiber70Block1Chunk1ParentPath_4_ok,
    tttLargeFiber70Block1Chunk1ParentPath_5_ok,
    tttLargeFiber70Block1Chunk1ParentPath_6_ok,
    tttLargeFiber70Block1Chunk1ParentPath_7_ok,
    tttLargeFiber70Block1Chunk1ParentPath_8_ok,
    tttLargeFiber70Block1Chunk1ParentPath_9_ok,
    tttLargeFiber70Block1Chunk1ParentPath_10_ok,
    tttLargeFiber70Block1Chunk1ParentPath_11_ok,
    tttLargeFiber70Block1Chunk1ParentPath_12_ok,
    tttLargeFiber70Block1Chunk1ParentPath_13_ok,
    tttLargeFiber70Block1Chunk1ParentPath_14_ok,
    tttLargeFiber70Block1Chunk1ParentPath_15_ok]

def tttLargeFiber70Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block1Chunk1SourcesCheck &&
    tttLargeFiber70Block1Chunk1RowsAudit &&
    tttLargeFiber70Block1Chunk1ParentMapAudit &&
    tttLargeFiber70Block1Chunk1ParentsAudit

theorem tttLargeFiber70Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber70Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block1Chunk1SourcesCheck_ok,
    tttLargeFiber70Block1Chunk1RowsAudit_ok,
    tttLargeFiber70Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber70Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
