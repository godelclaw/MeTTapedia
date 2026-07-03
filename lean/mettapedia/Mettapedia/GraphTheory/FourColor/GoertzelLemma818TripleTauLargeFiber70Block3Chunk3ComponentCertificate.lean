import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 3 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block3Chunk3Sources : List Nat :=
  [   2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967,
   2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975]

def tttLargeFiber70Row240 : TripleComponentParentRow :=
  tripleRow 2960 2832 83 42 0 81 110 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row241 : TripleComponentParentRow :=
  tripleRow 2961 2833 83 42 1 81 110 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row242 : TripleComponentParentRow :=
  tripleRow 2962 2834 83 42 2 81 110 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row243 : TripleComponentParentRow :=
  tripleRow 2963 2835 83 42 3 81 110 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row244 : TripleComponentParentRow :=
  tripleRow 2964 2960 83 42 48 83 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row245 : TripleComponentParentRow :=
  tripleRow 2965 2961 83 42 49 83 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row246 : TripleComponentParentRow :=
  tripleRow 2966 2838 83 42 50 81 110 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row247 : TripleComponentParentRow :=
  tripleRow 2967 2839 83 42 51 81 110 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row248 : TripleComponentParentRow :=
  tripleRow 2968 2840 83 43 8 81 111 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row249 : TripleComponentParentRow :=
  tripleRow 2969 2841 83 43 9 81 111 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row250 : TripleComponentParentRow :=
  tripleRow 2970 2842 83 43 10 81 111 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row251 : TripleComponentParentRow :=
  tripleRow 2971 2843 83 43 11 81 111 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row252 : TripleComponentParentRow :=
  tripleRow 2972 2968 83 43 56 83 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row253 : TripleComponentParentRow :=
  tripleRow 2973 2969 83 43 57 83 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row254 : TripleComponentParentRow :=
  tripleRow 2974 2846 83 43 58 81 111 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Row255 : TripleComponentParentRow :=
  tripleRow 2975 2847 83 43 59 81 111 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber70Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row240
  , tttLargeFiber70Row241
  , tttLargeFiber70Row242
  , tttLargeFiber70Row243
  , tttLargeFiber70Row244
  , tttLargeFiber70Row245
  , tttLargeFiber70Row246
  , tttLargeFiber70Row247
  , tttLargeFiber70Row248
  , tttLargeFiber70Row249
  , tttLargeFiber70Row250
  , tttLargeFiber70Row251
  , tttLargeFiber70Row252
  , tttLargeFiber70Row253
  , tttLargeFiber70Row254
  , tttLargeFiber70Row255
  ]

def tttLargeFiber70Block3Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block3Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block3Chunk3ExpectedContains row.source &&
    tttLargeFiber70Block3Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber70Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber70Block3Chunk3Sources

theorem tttLargeFiber70Block3Chunk3SourcesCheck_ok :
    tttLargeFiber70Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber70Block3Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block3Chunk3RowValid
    (listGetD tttLargeFiber70Block3Chunk3Rows i default)

def tttLargeFiber70Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block3Chunk3Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block3Chunk3Sources 0 0 == 2960
      && tttLargeFiber70ParentOf 2960 == 2832
      && tttLargeFiber70ParentOf 2832 == 2768
      && tttLargeFiber70ParentOf 2768 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block3Chunk3Sources 1 0 == 2961
      && tttLargeFiber70ParentOf 2961 == 2833
      && tttLargeFiber70ParentOf 2833 == 2769
      && tttLargeFiber70ParentOf 2769 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block3Chunk3Sources 2 0 == 2962
      && tttLargeFiber70ParentOf 2962 == 2834
      && tttLargeFiber70ParentOf 2834 == 2770
      && tttLargeFiber70ParentOf 2770 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block3Chunk3Sources 3 0 == 2963
      && tttLargeFiber70ParentOf 2963 == 2835
      && tttLargeFiber70ParentOf 2835 == 2771
      && tttLargeFiber70ParentOf 2771 == 2731
      && tttLargeFiber70ParentOf 2731 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block3Chunk3Sources 4 0 == 2964
      && tttLargeFiber70ParentOf 2964 == 2960
      && tttLargeFiber70ParentOf 2960 == 2832
      && tttLargeFiber70ParentOf 2832 == 2768
      && tttLargeFiber70ParentOf 2768 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block3Chunk3Sources 5 0 == 2965
      && tttLargeFiber70ParentOf 2965 == 2961
      && tttLargeFiber70ParentOf 2961 == 2833
      && tttLargeFiber70ParentOf 2833 == 2769
      && tttLargeFiber70ParentOf 2769 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block3Chunk3Sources 6 0 == 2966
      && tttLargeFiber70ParentOf 2966 == 2838
      && tttLargeFiber70ParentOf 2838 == 2774
      && tttLargeFiber70ParentOf 2774 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block3Chunk3Sources 7 0 == 2967
      && tttLargeFiber70ParentOf 2967 == 2839
      && tttLargeFiber70ParentOf 2839 == 2775
      && tttLargeFiber70ParentOf 2775 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block3Chunk3Sources 8 0 == 2968
      && tttLargeFiber70ParentOf 2968 == 2840
      && tttLargeFiber70ParentOf 2840 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block3Chunk3Sources 9 0 == 2969
      && tttLargeFiber70ParentOf 2969 == 2841
      && tttLargeFiber70ParentOf 2841 == 2777
      && tttLargeFiber70ParentOf 2777 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block3Chunk3Sources 10 0 == 2970
      && tttLargeFiber70ParentOf 2970 == 2842
      && tttLargeFiber70ParentOf 2842 == 2778
      && tttLargeFiber70ParentOf 2778 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block3Chunk3Sources 11 0 == 2971
      && tttLargeFiber70ParentOf 2971 == 2843
      && tttLargeFiber70ParentOf 2843 == 2779
      && tttLargeFiber70ParentOf 2779 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block3Chunk3Sources 12 0 == 2972
      && tttLargeFiber70ParentOf 2972 == 2968
      && tttLargeFiber70ParentOf 2968 == 2840
      && tttLargeFiber70ParentOf 2840 == 2776
      && tttLargeFiber70ParentOf 2776 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block3Chunk3Sources 13 0 == 2973
      && tttLargeFiber70ParentOf 2973 == 2969
      && tttLargeFiber70ParentOf 2969 == 2841
      && tttLargeFiber70ParentOf 2841 == 2777
      && tttLargeFiber70ParentOf 2777 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block3Chunk3Sources 14 0 == 2974
      && tttLargeFiber70ParentOf 2974 == 2846
      && tttLargeFiber70ParentOf 2846 == 2782
      && tttLargeFiber70ParentOf 2782 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block3Chunk3Sources 15 0 == 2975
      && tttLargeFiber70ParentOf 2975 == 2847
      && tttLargeFiber70ParentOf 2847 == 2783
      && tttLargeFiber70ParentOf 2783 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block3Chunk3Row_0_ok :
    tttLargeFiber70Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_1_ok :
    tttLargeFiber70Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_2_ok :
    tttLargeFiber70Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_3_ok :
    tttLargeFiber70Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_4_ok :
    tttLargeFiber70Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_5_ok :
    tttLargeFiber70Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_6_ok :
    tttLargeFiber70Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_7_ok :
    tttLargeFiber70Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_8_ok :
    tttLargeFiber70Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_9_ok :
    tttLargeFiber70Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_10_ok :
    tttLargeFiber70Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_11_ok :
    tttLargeFiber70Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_12_ok :
    tttLargeFiber70Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_13_ok :
    tttLargeFiber70Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_14_ok :
    tttLargeFiber70Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3Row_15_ok :
    tttLargeFiber70Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_0_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_1_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_2_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_3_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_4_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_5_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_6_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_7_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_8_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_9_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_10_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_11_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_12_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_13_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_14_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentMap_15_ok :
    tttLargeFiber70Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_0_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_1_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_2_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_3_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_4_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_5_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_6_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_7_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_8_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_9_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_10_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_11_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_12_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_13_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_14_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block3Chunk3ParentPath_15_ok :
    tttLargeFiber70Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber70Block3Chunk3RowCheck 0
    && tttLargeFiber70Block3Chunk3RowCheck 1
    && tttLargeFiber70Block3Chunk3RowCheck 2
    && tttLargeFiber70Block3Chunk3RowCheck 3
    && tttLargeFiber70Block3Chunk3RowCheck 4
    && tttLargeFiber70Block3Chunk3RowCheck 5
    && tttLargeFiber70Block3Chunk3RowCheck 6
    && tttLargeFiber70Block3Chunk3RowCheck 7
    && tttLargeFiber70Block3Chunk3RowCheck 8
    && tttLargeFiber70Block3Chunk3RowCheck 9
    && tttLargeFiber70Block3Chunk3RowCheck 10
    && tttLargeFiber70Block3Chunk3RowCheck 11
    && tttLargeFiber70Block3Chunk3RowCheck 12
    && tttLargeFiber70Block3Chunk3RowCheck 13
    && tttLargeFiber70Block3Chunk3RowCheck 14
    && tttLargeFiber70Block3Chunk3RowCheck 15

theorem tttLargeFiber70Block3Chunk3RowsAudit_ok :
    tttLargeFiber70Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber70Block3Chunk3RowsAudit,
    tttLargeFiber70Block3Chunk3Row_0_ok,
    tttLargeFiber70Block3Chunk3Row_1_ok,
    tttLargeFiber70Block3Chunk3Row_2_ok,
    tttLargeFiber70Block3Chunk3Row_3_ok,
    tttLargeFiber70Block3Chunk3Row_4_ok,
    tttLargeFiber70Block3Chunk3Row_5_ok,
    tttLargeFiber70Block3Chunk3Row_6_ok,
    tttLargeFiber70Block3Chunk3Row_7_ok,
    tttLargeFiber70Block3Chunk3Row_8_ok,
    tttLargeFiber70Block3Chunk3Row_9_ok,
    tttLargeFiber70Block3Chunk3Row_10_ok,
    tttLargeFiber70Block3Chunk3Row_11_ok,
    tttLargeFiber70Block3Chunk3Row_12_ok,
    tttLargeFiber70Block3Chunk3Row_13_ok,
    tttLargeFiber70Block3Chunk3Row_14_ok,
    tttLargeFiber70Block3Chunk3Row_15_ok]

def tttLargeFiber70Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber70Block3Chunk3ParentMapCheck 0
    && tttLargeFiber70Block3Chunk3ParentMapCheck 1
    && tttLargeFiber70Block3Chunk3ParentMapCheck 2
    && tttLargeFiber70Block3Chunk3ParentMapCheck 3
    && tttLargeFiber70Block3Chunk3ParentMapCheck 4
    && tttLargeFiber70Block3Chunk3ParentMapCheck 5
    && tttLargeFiber70Block3Chunk3ParentMapCheck 6
    && tttLargeFiber70Block3Chunk3ParentMapCheck 7
    && tttLargeFiber70Block3Chunk3ParentMapCheck 8
    && tttLargeFiber70Block3Chunk3ParentMapCheck 9
    && tttLargeFiber70Block3Chunk3ParentMapCheck 10
    && tttLargeFiber70Block3Chunk3ParentMapCheck 11
    && tttLargeFiber70Block3Chunk3ParentMapCheck 12
    && tttLargeFiber70Block3Chunk3ParentMapCheck 13
    && tttLargeFiber70Block3Chunk3ParentMapCheck 14
    && tttLargeFiber70Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber70Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber70Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber70Block3Chunk3ParentMapAudit,
    tttLargeFiber70Block3Chunk3ParentMap_0_ok,
    tttLargeFiber70Block3Chunk3ParentMap_1_ok,
    tttLargeFiber70Block3Chunk3ParentMap_2_ok,
    tttLargeFiber70Block3Chunk3ParentMap_3_ok,
    tttLargeFiber70Block3Chunk3ParentMap_4_ok,
    tttLargeFiber70Block3Chunk3ParentMap_5_ok,
    tttLargeFiber70Block3Chunk3ParentMap_6_ok,
    tttLargeFiber70Block3Chunk3ParentMap_7_ok,
    tttLargeFiber70Block3Chunk3ParentMap_8_ok,
    tttLargeFiber70Block3Chunk3ParentMap_9_ok,
    tttLargeFiber70Block3Chunk3ParentMap_10_ok,
    tttLargeFiber70Block3Chunk3ParentMap_11_ok,
    tttLargeFiber70Block3Chunk3ParentMap_12_ok,
    tttLargeFiber70Block3Chunk3ParentMap_13_ok,
    tttLargeFiber70Block3Chunk3ParentMap_14_ok,
    tttLargeFiber70Block3Chunk3ParentMap_15_ok]

def tttLargeFiber70Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber70Block3Chunk3ParentPathCheck 0
    && tttLargeFiber70Block3Chunk3ParentPathCheck 1
    && tttLargeFiber70Block3Chunk3ParentPathCheck 2
    && tttLargeFiber70Block3Chunk3ParentPathCheck 3
    && tttLargeFiber70Block3Chunk3ParentPathCheck 4
    && tttLargeFiber70Block3Chunk3ParentPathCheck 5
    && tttLargeFiber70Block3Chunk3ParentPathCheck 6
    && tttLargeFiber70Block3Chunk3ParentPathCheck 7
    && tttLargeFiber70Block3Chunk3ParentPathCheck 8
    && tttLargeFiber70Block3Chunk3ParentPathCheck 9
    && tttLargeFiber70Block3Chunk3ParentPathCheck 10
    && tttLargeFiber70Block3Chunk3ParentPathCheck 11
    && tttLargeFiber70Block3Chunk3ParentPathCheck 12
    && tttLargeFiber70Block3Chunk3ParentPathCheck 13
    && tttLargeFiber70Block3Chunk3ParentPathCheck 14
    && tttLargeFiber70Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber70Block3Chunk3ParentsAudit_ok :
    tttLargeFiber70Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber70Block3Chunk3ParentsAudit,
    tttLargeFiber70Block3Chunk3ParentPath_0_ok,
    tttLargeFiber70Block3Chunk3ParentPath_1_ok,
    tttLargeFiber70Block3Chunk3ParentPath_2_ok,
    tttLargeFiber70Block3Chunk3ParentPath_3_ok,
    tttLargeFiber70Block3Chunk3ParentPath_4_ok,
    tttLargeFiber70Block3Chunk3ParentPath_5_ok,
    tttLargeFiber70Block3Chunk3ParentPath_6_ok,
    tttLargeFiber70Block3Chunk3ParentPath_7_ok,
    tttLargeFiber70Block3Chunk3ParentPath_8_ok,
    tttLargeFiber70Block3Chunk3ParentPath_9_ok,
    tttLargeFiber70Block3Chunk3ParentPath_10_ok,
    tttLargeFiber70Block3Chunk3ParentPath_11_ok,
    tttLargeFiber70Block3Chunk3ParentPath_12_ok,
    tttLargeFiber70Block3Chunk3ParentPath_13_ok,
    tttLargeFiber70Block3Chunk3ParentPath_14_ok,
    tttLargeFiber70Block3Chunk3ParentPath_15_ok]

def tttLargeFiber70Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block3Chunk3SourcesCheck &&
    tttLargeFiber70Block3Chunk3RowsAudit &&
    tttLargeFiber70Block3Chunk3ParentMapAudit &&
    tttLargeFiber70Block3Chunk3ParentsAudit

theorem tttLargeFiber70Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber70Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block3Chunk3SourcesCheck_ok,
    tttLargeFiber70Block3Chunk3RowsAudit_ok,
    tttLargeFiber70Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber70Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
