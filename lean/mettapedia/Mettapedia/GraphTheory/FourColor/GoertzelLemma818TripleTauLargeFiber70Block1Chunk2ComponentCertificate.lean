import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block1Chunk2Sources : List Nat :=
  [   2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823,
   2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831]

def tttLargeFiber70Row96 : TripleComponentParentRow :=
  tripleRow 2816 2752 81 108 132 80 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row97 : TripleComponentParentRow :=
  tripleRow 2817 2753 81 108 133 80 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row98 : TripleComponentParentRow :=
  tripleRow 2818 2754 81 108 134 80 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row99 : TripleComponentParentRow :=
  tripleRow 2819 2755 81 108 135 80 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row100 : TripleComponentParentRow :=
  tripleRow 2820 2756 81 108 180 80 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row101 : TripleComponentParentRow :=
  tripleRow 2821 2757 81 108 181 80 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row102 : TripleComponentParentRow :=
  tripleRow 2822 2758 81 108 182 80 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row103 : TripleComponentParentRow :=
  tripleRow 2823 2759 81 108 183 80 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row104 : TripleComponentParentRow :=
  tripleRow 2824 2760 81 109 140 80 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row105 : TripleComponentParentRow :=
  tripleRow 2825 2761 81 109 141 80 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row106 : TripleComponentParentRow :=
  tripleRow 2826 2762 81 109 142 80 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row107 : TripleComponentParentRow :=
  tripleRow 2827 2763 81 109 143 80 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row108 : TripleComponentParentRow :=
  tripleRow 2828 2764 81 109 188 80 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row109 : TripleComponentParentRow :=
  tripleRow 2829 2765 81 109 189 80 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row110 : TripleComponentParentRow :=
  tripleRow 2830 2766 81 109 190 80 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Row111 : TripleComponentParentRow :=
  tripleRow 2831 2767 81 109 191 80 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber70Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row96
  , tttLargeFiber70Row97
  , tttLargeFiber70Row98
  , tttLargeFiber70Row99
  , tttLargeFiber70Row100
  , tttLargeFiber70Row101
  , tttLargeFiber70Row102
  , tttLargeFiber70Row103
  , tttLargeFiber70Row104
  , tttLargeFiber70Row105
  , tttLargeFiber70Row106
  , tttLargeFiber70Row107
  , tttLargeFiber70Row108
  , tttLargeFiber70Row109
  , tttLargeFiber70Row110
  , tttLargeFiber70Row111
  ]

def tttLargeFiber70Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber70Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber70Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber70Block1Chunk2Sources

theorem tttLargeFiber70Block1Chunk2SourcesCheck_ok :
    tttLargeFiber70Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber70Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block1Chunk2RowValid
    (listGetD tttLargeFiber70Block1Chunk2Rows i default)

def tttLargeFiber70Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block1Chunk2Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block1Chunk2Sources 0 0 == 2816
      && tttLargeFiber70ParentOf 2816 == 2752
      && tttLargeFiber70ParentOf 2752 == 2768
      && tttLargeFiber70ParentOf 2768 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block1Chunk2Sources 1 0 == 2817
      && tttLargeFiber70ParentOf 2817 == 2753
      && tttLargeFiber70ParentOf 2753 == 2769
      && tttLargeFiber70ParentOf 2769 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block1Chunk2Sources 2 0 == 2818
      && tttLargeFiber70ParentOf 2818 == 2754
      && tttLargeFiber70ParentOf 2754 == 2742
      && tttLargeFiber70ParentOf 2742 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block1Chunk2Sources 3 0 == 2819
      && tttLargeFiber70ParentOf 2819 == 2755
      && tttLargeFiber70ParentOf 2755 == 2743
      && tttLargeFiber70ParentOf 2743 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block1Chunk2Sources 4 0 == 2820
      && tttLargeFiber70ParentOf 2820 == 2756
      && tttLargeFiber70ParentOf 2756 == 2738
      && tttLargeFiber70ParentOf 2738 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block1Chunk2Sources 5 0 == 2821
      && tttLargeFiber70ParentOf 2821 == 2757
      && tttLargeFiber70ParentOf 2757 == 2759
      && tttLargeFiber70ParentOf 2759 == 2736
      && tttLargeFiber70ParentOf 2736 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block1Chunk2Sources 6 0 == 2822
      && tttLargeFiber70ParentOf 2822 == 2758
      && tttLargeFiber70ParentOf 2758 == 2737
      && tttLargeFiber70ParentOf 2737 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block1Chunk2Sources 7 0 == 2823
      && tttLargeFiber70ParentOf 2823 == 2759
      && tttLargeFiber70ParentOf 2759 == 2736
      && tttLargeFiber70ParentOf 2736 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block1Chunk2Sources 8 0 == 2824
      && tttLargeFiber70ParentOf 2824 == 2760
      && tttLargeFiber70ParentOf 2760 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block1Chunk2Sources 9 0 == 2825
      && tttLargeFiber70ParentOf 2825 == 2761
      && tttLargeFiber70ParentOf 2761 == 2777
      && tttLargeFiber70ParentOf 2777 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block1Chunk2Sources 10 0 == 2826
      && tttLargeFiber70ParentOf 2826 == 2762
      && tttLargeFiber70ParentOf 2762 == 2778
      && tttLargeFiber70ParentOf 2778 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block1Chunk2Sources 11 0 == 2827
      && tttLargeFiber70ParentOf 2827 == 2763
      && tttLargeFiber70ParentOf 2763 == 2760
      && tttLargeFiber70ParentOf 2760 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block1Chunk2Sources 12 0 == 2828
      && tttLargeFiber70ParentOf 2828 == 2764
      && tttLargeFiber70ParentOf 2764 == 2760
      && tttLargeFiber70ParentOf 2760 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block1Chunk2Sources 13 0 == 2829
      && tttLargeFiber70ParentOf 2829 == 2765
      && tttLargeFiber70ParentOf 2765 == 2761
      && tttLargeFiber70ParentOf 2761 == 2777
      && tttLargeFiber70ParentOf 2777 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block1Chunk2Sources 14 0 == 2830
      && tttLargeFiber70ParentOf 2830 == 2766
      && tttLargeFiber70ParentOf 2766 == 2782
      && tttLargeFiber70ParentOf 2782 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block1Chunk2Sources 15 0 == 2831
      && tttLargeFiber70ParentOf 2831 == 2767
      && tttLargeFiber70ParentOf 2767 == 2783
      && tttLargeFiber70ParentOf 2783 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block1Chunk2Row_0_ok :
    tttLargeFiber70Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_1_ok :
    tttLargeFiber70Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_2_ok :
    tttLargeFiber70Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_3_ok :
    tttLargeFiber70Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_4_ok :
    tttLargeFiber70Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_5_ok :
    tttLargeFiber70Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_6_ok :
    tttLargeFiber70Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_7_ok :
    tttLargeFiber70Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_8_ok :
    tttLargeFiber70Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_9_ok :
    tttLargeFiber70Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_10_ok :
    tttLargeFiber70Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_11_ok :
    tttLargeFiber70Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_12_ok :
    tttLargeFiber70Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_13_ok :
    tttLargeFiber70Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_14_ok :
    tttLargeFiber70Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2Row_15_ok :
    tttLargeFiber70Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_0_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_1_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_2_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_3_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_4_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_5_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_6_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_7_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_8_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_9_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_10_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_11_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_12_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_13_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_14_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentMap_15_ok :
    tttLargeFiber70Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_0_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_1_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_2_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_3_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_4_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_5_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_6_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_7_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_8_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_9_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_10_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_11_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_12_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_13_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_14_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block1Chunk2ParentPath_15_ok :
    tttLargeFiber70Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber70Block1Chunk2RowCheck 0
    && tttLargeFiber70Block1Chunk2RowCheck 1
    && tttLargeFiber70Block1Chunk2RowCheck 2
    && tttLargeFiber70Block1Chunk2RowCheck 3
    && tttLargeFiber70Block1Chunk2RowCheck 4
    && tttLargeFiber70Block1Chunk2RowCheck 5
    && tttLargeFiber70Block1Chunk2RowCheck 6
    && tttLargeFiber70Block1Chunk2RowCheck 7
    && tttLargeFiber70Block1Chunk2RowCheck 8
    && tttLargeFiber70Block1Chunk2RowCheck 9
    && tttLargeFiber70Block1Chunk2RowCheck 10
    && tttLargeFiber70Block1Chunk2RowCheck 11
    && tttLargeFiber70Block1Chunk2RowCheck 12
    && tttLargeFiber70Block1Chunk2RowCheck 13
    && tttLargeFiber70Block1Chunk2RowCheck 14
    && tttLargeFiber70Block1Chunk2RowCheck 15

theorem tttLargeFiber70Block1Chunk2RowsAudit_ok :
    tttLargeFiber70Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber70Block1Chunk2RowsAudit,
    tttLargeFiber70Block1Chunk2Row_0_ok,
    tttLargeFiber70Block1Chunk2Row_1_ok,
    tttLargeFiber70Block1Chunk2Row_2_ok,
    tttLargeFiber70Block1Chunk2Row_3_ok,
    tttLargeFiber70Block1Chunk2Row_4_ok,
    tttLargeFiber70Block1Chunk2Row_5_ok,
    tttLargeFiber70Block1Chunk2Row_6_ok,
    tttLargeFiber70Block1Chunk2Row_7_ok,
    tttLargeFiber70Block1Chunk2Row_8_ok,
    tttLargeFiber70Block1Chunk2Row_9_ok,
    tttLargeFiber70Block1Chunk2Row_10_ok,
    tttLargeFiber70Block1Chunk2Row_11_ok,
    tttLargeFiber70Block1Chunk2Row_12_ok,
    tttLargeFiber70Block1Chunk2Row_13_ok,
    tttLargeFiber70Block1Chunk2Row_14_ok,
    tttLargeFiber70Block1Chunk2Row_15_ok]

def tttLargeFiber70Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber70Block1Chunk2ParentMapCheck 0
    && tttLargeFiber70Block1Chunk2ParentMapCheck 1
    && tttLargeFiber70Block1Chunk2ParentMapCheck 2
    && tttLargeFiber70Block1Chunk2ParentMapCheck 3
    && tttLargeFiber70Block1Chunk2ParentMapCheck 4
    && tttLargeFiber70Block1Chunk2ParentMapCheck 5
    && tttLargeFiber70Block1Chunk2ParentMapCheck 6
    && tttLargeFiber70Block1Chunk2ParentMapCheck 7
    && tttLargeFiber70Block1Chunk2ParentMapCheck 8
    && tttLargeFiber70Block1Chunk2ParentMapCheck 9
    && tttLargeFiber70Block1Chunk2ParentMapCheck 10
    && tttLargeFiber70Block1Chunk2ParentMapCheck 11
    && tttLargeFiber70Block1Chunk2ParentMapCheck 12
    && tttLargeFiber70Block1Chunk2ParentMapCheck 13
    && tttLargeFiber70Block1Chunk2ParentMapCheck 14
    && tttLargeFiber70Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber70Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber70Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber70Block1Chunk2ParentMapAudit,
    tttLargeFiber70Block1Chunk2ParentMap_0_ok,
    tttLargeFiber70Block1Chunk2ParentMap_1_ok,
    tttLargeFiber70Block1Chunk2ParentMap_2_ok,
    tttLargeFiber70Block1Chunk2ParentMap_3_ok,
    tttLargeFiber70Block1Chunk2ParentMap_4_ok,
    tttLargeFiber70Block1Chunk2ParentMap_5_ok,
    tttLargeFiber70Block1Chunk2ParentMap_6_ok,
    tttLargeFiber70Block1Chunk2ParentMap_7_ok,
    tttLargeFiber70Block1Chunk2ParentMap_8_ok,
    tttLargeFiber70Block1Chunk2ParentMap_9_ok,
    tttLargeFiber70Block1Chunk2ParentMap_10_ok,
    tttLargeFiber70Block1Chunk2ParentMap_11_ok,
    tttLargeFiber70Block1Chunk2ParentMap_12_ok,
    tttLargeFiber70Block1Chunk2ParentMap_13_ok,
    tttLargeFiber70Block1Chunk2ParentMap_14_ok,
    tttLargeFiber70Block1Chunk2ParentMap_15_ok]

def tttLargeFiber70Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber70Block1Chunk2ParentPathCheck 0
    && tttLargeFiber70Block1Chunk2ParentPathCheck 1
    && tttLargeFiber70Block1Chunk2ParentPathCheck 2
    && tttLargeFiber70Block1Chunk2ParentPathCheck 3
    && tttLargeFiber70Block1Chunk2ParentPathCheck 4
    && tttLargeFiber70Block1Chunk2ParentPathCheck 5
    && tttLargeFiber70Block1Chunk2ParentPathCheck 6
    && tttLargeFiber70Block1Chunk2ParentPathCheck 7
    && tttLargeFiber70Block1Chunk2ParentPathCheck 8
    && tttLargeFiber70Block1Chunk2ParentPathCheck 9
    && tttLargeFiber70Block1Chunk2ParentPathCheck 10
    && tttLargeFiber70Block1Chunk2ParentPathCheck 11
    && tttLargeFiber70Block1Chunk2ParentPathCheck 12
    && tttLargeFiber70Block1Chunk2ParentPathCheck 13
    && tttLargeFiber70Block1Chunk2ParentPathCheck 14
    && tttLargeFiber70Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber70Block1Chunk2ParentsAudit_ok :
    tttLargeFiber70Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber70Block1Chunk2ParentsAudit,
    tttLargeFiber70Block1Chunk2ParentPath_0_ok,
    tttLargeFiber70Block1Chunk2ParentPath_1_ok,
    tttLargeFiber70Block1Chunk2ParentPath_2_ok,
    tttLargeFiber70Block1Chunk2ParentPath_3_ok,
    tttLargeFiber70Block1Chunk2ParentPath_4_ok,
    tttLargeFiber70Block1Chunk2ParentPath_5_ok,
    tttLargeFiber70Block1Chunk2ParentPath_6_ok,
    tttLargeFiber70Block1Chunk2ParentPath_7_ok,
    tttLargeFiber70Block1Chunk2ParentPath_8_ok,
    tttLargeFiber70Block1Chunk2ParentPath_9_ok,
    tttLargeFiber70Block1Chunk2ParentPath_10_ok,
    tttLargeFiber70Block1Chunk2ParentPath_11_ok,
    tttLargeFiber70Block1Chunk2ParentPath_12_ok,
    tttLargeFiber70Block1Chunk2ParentPath_13_ok,
    tttLargeFiber70Block1Chunk2ParentPath_14_ok,
    tttLargeFiber70Block1Chunk2ParentPath_15_ok]

def tttLargeFiber70Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block1Chunk2SourcesCheck &&
    tttLargeFiber70Block1Chunk2RowsAudit &&
    tttLargeFiber70Block1Chunk2ParentMapAudit &&
    tttLargeFiber70Block1Chunk2ParentsAudit

theorem tttLargeFiber70Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber70Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block1Chunk2SourcesCheck_ok,
    tttLargeFiber70Block1Chunk2RowsAudit_ok,
    tttLargeFiber70Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber70Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
