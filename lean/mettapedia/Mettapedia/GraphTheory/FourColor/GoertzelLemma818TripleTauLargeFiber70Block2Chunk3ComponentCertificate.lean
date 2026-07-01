import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 2 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block2Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block2Chunk3Sources : List Nat :=
  [   2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903,
   2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]

def tttLargeFiber70Row176 : TripleComponentParentRow :=
  tripleRow 2896 2768 82 34 0 80 102 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row177 : TripleComponentParentRow :=
  tripleRow 2897 2769 82 34 1 80 102 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row178 : TripleComponentParentRow :=
  tripleRow 2898 2770 82 34 2 80 102 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row179 : TripleComponentParentRow :=
  tripleRow 2899 2771 82 34 3 80 102 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row180 : TripleComponentParentRow :=
  tripleRow 2900 2896 82 34 48 82 34 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row181 : TripleComponentParentRow :=
  tripleRow 2901 2897 82 34 49 82 34 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row182 : TripleComponentParentRow :=
  tripleRow 2902 2774 82 34 50 80 102 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row183 : TripleComponentParentRow :=
  tripleRow 2903 2775 82 34 51 80 102 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row184 : TripleComponentParentRow :=
  tripleRow 2904 2776 82 35 8 80 103 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row185 : TripleComponentParentRow :=
  tripleRow 2905 2777 82 35 9 80 103 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row186 : TripleComponentParentRow :=
  tripleRow 2906 2778 82 35 10 80 103 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row187 : TripleComponentParentRow :=
  tripleRow 2907 2779 82 35 11 80 103 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row188 : TripleComponentParentRow :=
  tripleRow 2908 2904 82 35 56 82 35 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row189 : TripleComponentParentRow :=
  tripleRow 2909 2905 82 35 57 82 35 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row190 : TripleComponentParentRow :=
  tripleRow 2910 2782 82 35 58 80 103 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row191 : TripleComponentParentRow :=
  tripleRow 2911 2783 82 35 59 80 103 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Block2Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row176
  , tttLargeFiber70Row177
  , tttLargeFiber70Row178
  , tttLargeFiber70Row179
  , tttLargeFiber70Row180
  , tttLargeFiber70Row181
  , tttLargeFiber70Row182
  , tttLargeFiber70Row183
  , tttLargeFiber70Row184
  , tttLargeFiber70Row185
  , tttLargeFiber70Row186
  , tttLargeFiber70Row187
  , tttLargeFiber70Row188
  , tttLargeFiber70Row189
  , tttLargeFiber70Row190
  , tttLargeFiber70Row191
  ]

def tttLargeFiber70Block2Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block2Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block2Chunk3ExpectedContains row.source &&
    tttLargeFiber70Block2Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block2Chunk3SourcesCheck : Bool :=
  (tttLargeFiber70Block2Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber70Block2Chunk3Sources

theorem tttLargeFiber70Block2Chunk3SourcesCheck_ok :
    tttLargeFiber70Block2Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber70Block2Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block2Chunk3RowValid
    (listGetD tttLargeFiber70Block2Chunk3Rows i default)

def tttLargeFiber70Block2Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block2Chunk3Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block2Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block2Chunk3Sources 0 0 == 2896
      && tttLargeFiber70ParentOf 2896 == 2768
      && tttLargeFiber70ParentOf 2768 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block2Chunk3Sources 1 0 == 2897
      && tttLargeFiber70ParentOf 2897 == 2769
      && tttLargeFiber70ParentOf 2769 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block2Chunk3Sources 2 0 == 2898
      && tttLargeFiber70ParentOf 2898 == 2770
      && tttLargeFiber70ParentOf 2770 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block2Chunk3Sources 3 0 == 2899
      && tttLargeFiber70ParentOf 2899 == 2771
      && tttLargeFiber70ParentOf 2771 == 2731
      && tttLargeFiber70ParentOf 2731 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block2Chunk3Sources 4 0 == 2900
      && tttLargeFiber70ParentOf 2900 == 2896
      && tttLargeFiber70ParentOf 2896 == 2768
      && tttLargeFiber70ParentOf 2768 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block2Chunk3Sources 5 0 == 2901
      && tttLargeFiber70ParentOf 2901 == 2897
      && tttLargeFiber70ParentOf 2897 == 2769
      && tttLargeFiber70ParentOf 2769 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block2Chunk3Sources 6 0 == 2902
      && tttLargeFiber70ParentOf 2902 == 2774
      && tttLargeFiber70ParentOf 2774 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block2Chunk3Sources 7 0 == 2903
      && tttLargeFiber70ParentOf 2903 == 2775
      && tttLargeFiber70ParentOf 2775 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block2Chunk3Sources 8 0 == 2904
      && tttLargeFiber70ParentOf 2904 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block2Chunk3Sources 9 0 == 2905
      && tttLargeFiber70ParentOf 2905 == 2777
      && tttLargeFiber70ParentOf 2777 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block2Chunk3Sources 10 0 == 2906
      && tttLargeFiber70ParentOf 2906 == 2778
      && tttLargeFiber70ParentOf 2778 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block2Chunk3Sources 11 0 == 2907
      && tttLargeFiber70ParentOf 2907 == 2779
      && tttLargeFiber70ParentOf 2779 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block2Chunk3Sources 12 0 == 2908
      && tttLargeFiber70ParentOf 2908 == 2904
      && tttLargeFiber70ParentOf 2904 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block2Chunk3Sources 13 0 == 2909
      && tttLargeFiber70ParentOf 2909 == 2905
      && tttLargeFiber70ParentOf 2905 == 2777
      && tttLargeFiber70ParentOf 2777 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block2Chunk3Sources 14 0 == 2910
      && tttLargeFiber70ParentOf 2910 == 2782
      && tttLargeFiber70ParentOf 2782 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block2Chunk3Sources 15 0 == 2911
      && tttLargeFiber70ParentOf 2911 == 2783
      && tttLargeFiber70ParentOf 2783 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block2Chunk3Row_0_ok :
    tttLargeFiber70Block2Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_1_ok :
    tttLargeFiber70Block2Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_2_ok :
    tttLargeFiber70Block2Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_3_ok :
    tttLargeFiber70Block2Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_4_ok :
    tttLargeFiber70Block2Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_5_ok :
    tttLargeFiber70Block2Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_6_ok :
    tttLargeFiber70Block2Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_7_ok :
    tttLargeFiber70Block2Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_8_ok :
    tttLargeFiber70Block2Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_9_ok :
    tttLargeFiber70Block2Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_10_ok :
    tttLargeFiber70Block2Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_11_ok :
    tttLargeFiber70Block2Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_12_ok :
    tttLargeFiber70Block2Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_13_ok :
    tttLargeFiber70Block2Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_14_ok :
    tttLargeFiber70Block2Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3Row_15_ok :
    tttLargeFiber70Block2Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_0_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_1_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_2_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_3_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_4_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_5_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_6_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_7_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_8_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_9_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_10_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_11_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_12_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_13_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_14_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentMap_15_ok :
    tttLargeFiber70Block2Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_0_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_1_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_2_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_3_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_4_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_5_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_6_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_7_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_8_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_9_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_10_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_11_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_12_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_13_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_14_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block2Chunk3ParentPath_15_ok :
    tttLargeFiber70Block2Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block2Chunk3RowsAudit : Bool :=
  tttLargeFiber70Block2Chunk3RowCheck 0
    && tttLargeFiber70Block2Chunk3RowCheck 1
    && tttLargeFiber70Block2Chunk3RowCheck 2
    && tttLargeFiber70Block2Chunk3RowCheck 3
    && tttLargeFiber70Block2Chunk3RowCheck 4
    && tttLargeFiber70Block2Chunk3RowCheck 5
    && tttLargeFiber70Block2Chunk3RowCheck 6
    && tttLargeFiber70Block2Chunk3RowCheck 7
    && tttLargeFiber70Block2Chunk3RowCheck 8
    && tttLargeFiber70Block2Chunk3RowCheck 9
    && tttLargeFiber70Block2Chunk3RowCheck 10
    && tttLargeFiber70Block2Chunk3RowCheck 11
    && tttLargeFiber70Block2Chunk3RowCheck 12
    && tttLargeFiber70Block2Chunk3RowCheck 13
    && tttLargeFiber70Block2Chunk3RowCheck 14
    && tttLargeFiber70Block2Chunk3RowCheck 15

theorem tttLargeFiber70Block2Chunk3RowsAudit_ok :
    tttLargeFiber70Block2Chunk3RowsAudit = true := by
  simp [tttLargeFiber70Block2Chunk3RowsAudit,
    tttLargeFiber70Block2Chunk3Row_0_ok,
    tttLargeFiber70Block2Chunk3Row_1_ok,
    tttLargeFiber70Block2Chunk3Row_2_ok,
    tttLargeFiber70Block2Chunk3Row_3_ok,
    tttLargeFiber70Block2Chunk3Row_4_ok,
    tttLargeFiber70Block2Chunk3Row_5_ok,
    tttLargeFiber70Block2Chunk3Row_6_ok,
    tttLargeFiber70Block2Chunk3Row_7_ok,
    tttLargeFiber70Block2Chunk3Row_8_ok,
    tttLargeFiber70Block2Chunk3Row_9_ok,
    tttLargeFiber70Block2Chunk3Row_10_ok,
    tttLargeFiber70Block2Chunk3Row_11_ok,
    tttLargeFiber70Block2Chunk3Row_12_ok,
    tttLargeFiber70Block2Chunk3Row_13_ok,
    tttLargeFiber70Block2Chunk3Row_14_ok,
    tttLargeFiber70Block2Chunk3Row_15_ok]

def tttLargeFiber70Block2Chunk3ParentMapAudit : Bool :=
  tttLargeFiber70Block2Chunk3ParentMapCheck 0
    && tttLargeFiber70Block2Chunk3ParentMapCheck 1
    && tttLargeFiber70Block2Chunk3ParentMapCheck 2
    && tttLargeFiber70Block2Chunk3ParentMapCheck 3
    && tttLargeFiber70Block2Chunk3ParentMapCheck 4
    && tttLargeFiber70Block2Chunk3ParentMapCheck 5
    && tttLargeFiber70Block2Chunk3ParentMapCheck 6
    && tttLargeFiber70Block2Chunk3ParentMapCheck 7
    && tttLargeFiber70Block2Chunk3ParentMapCheck 8
    && tttLargeFiber70Block2Chunk3ParentMapCheck 9
    && tttLargeFiber70Block2Chunk3ParentMapCheck 10
    && tttLargeFiber70Block2Chunk3ParentMapCheck 11
    && tttLargeFiber70Block2Chunk3ParentMapCheck 12
    && tttLargeFiber70Block2Chunk3ParentMapCheck 13
    && tttLargeFiber70Block2Chunk3ParentMapCheck 14
    && tttLargeFiber70Block2Chunk3ParentMapCheck 15

theorem tttLargeFiber70Block2Chunk3ParentMapAudit_ok :
    tttLargeFiber70Block2Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber70Block2Chunk3ParentMapAudit,
    tttLargeFiber70Block2Chunk3ParentMap_0_ok,
    tttLargeFiber70Block2Chunk3ParentMap_1_ok,
    tttLargeFiber70Block2Chunk3ParentMap_2_ok,
    tttLargeFiber70Block2Chunk3ParentMap_3_ok,
    tttLargeFiber70Block2Chunk3ParentMap_4_ok,
    tttLargeFiber70Block2Chunk3ParentMap_5_ok,
    tttLargeFiber70Block2Chunk3ParentMap_6_ok,
    tttLargeFiber70Block2Chunk3ParentMap_7_ok,
    tttLargeFiber70Block2Chunk3ParentMap_8_ok,
    tttLargeFiber70Block2Chunk3ParentMap_9_ok,
    tttLargeFiber70Block2Chunk3ParentMap_10_ok,
    tttLargeFiber70Block2Chunk3ParentMap_11_ok,
    tttLargeFiber70Block2Chunk3ParentMap_12_ok,
    tttLargeFiber70Block2Chunk3ParentMap_13_ok,
    tttLargeFiber70Block2Chunk3ParentMap_14_ok,
    tttLargeFiber70Block2Chunk3ParentMap_15_ok]

def tttLargeFiber70Block2Chunk3ParentsAudit : Bool :=
  tttLargeFiber70Block2Chunk3ParentPathCheck 0
    && tttLargeFiber70Block2Chunk3ParentPathCheck 1
    && tttLargeFiber70Block2Chunk3ParentPathCheck 2
    && tttLargeFiber70Block2Chunk3ParentPathCheck 3
    && tttLargeFiber70Block2Chunk3ParentPathCheck 4
    && tttLargeFiber70Block2Chunk3ParentPathCheck 5
    && tttLargeFiber70Block2Chunk3ParentPathCheck 6
    && tttLargeFiber70Block2Chunk3ParentPathCheck 7
    && tttLargeFiber70Block2Chunk3ParentPathCheck 8
    && tttLargeFiber70Block2Chunk3ParentPathCheck 9
    && tttLargeFiber70Block2Chunk3ParentPathCheck 10
    && tttLargeFiber70Block2Chunk3ParentPathCheck 11
    && tttLargeFiber70Block2Chunk3ParentPathCheck 12
    && tttLargeFiber70Block2Chunk3ParentPathCheck 13
    && tttLargeFiber70Block2Chunk3ParentPathCheck 14
    && tttLargeFiber70Block2Chunk3ParentPathCheck 15

theorem tttLargeFiber70Block2Chunk3ParentsAudit_ok :
    tttLargeFiber70Block2Chunk3ParentsAudit = true := by
  simp [tttLargeFiber70Block2Chunk3ParentsAudit,
    tttLargeFiber70Block2Chunk3ParentPath_0_ok,
    tttLargeFiber70Block2Chunk3ParentPath_1_ok,
    tttLargeFiber70Block2Chunk3ParentPath_2_ok,
    tttLargeFiber70Block2Chunk3ParentPath_3_ok,
    tttLargeFiber70Block2Chunk3ParentPath_4_ok,
    tttLargeFiber70Block2Chunk3ParentPath_5_ok,
    tttLargeFiber70Block2Chunk3ParentPath_6_ok,
    tttLargeFiber70Block2Chunk3ParentPath_7_ok,
    tttLargeFiber70Block2Chunk3ParentPath_8_ok,
    tttLargeFiber70Block2Chunk3ParentPath_9_ok,
    tttLargeFiber70Block2Chunk3ParentPath_10_ok,
    tttLargeFiber70Block2Chunk3ParentPath_11_ok,
    tttLargeFiber70Block2Chunk3ParentPath_12_ok,
    tttLargeFiber70Block2Chunk3ParentPath_13_ok,
    tttLargeFiber70Block2Chunk3ParentPath_14_ok,
    tttLargeFiber70Block2Chunk3ParentPath_15_ok]

def tttLargeFiber70Block2Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block2Chunk3SourcesCheck &&
    tttLargeFiber70Block2Chunk3RowsAudit &&
    tttLargeFiber70Block2Chunk3ParentMapAudit &&
    tttLargeFiber70Block2Chunk3ParentsAudit

theorem tttLargeFiber70Block2Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber70Block2Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block2Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block2Chunk3SourcesCheck_ok,
    tttLargeFiber70Block2Chunk3RowsAudit_ok,
    tttLargeFiber70Block2Chunk3ParentMapAudit_ok,
    tttLargeFiber70Block2Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block2Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
