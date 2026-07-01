import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 3 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block3Chunk2Sources : List Nat :=
  [   2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951,
   2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]

def tttLargeFiber70Row224 : TripleComponentParentRow :=
  tripleRow 2944 2912 83 40 148 83 24 80
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

def tttLargeFiber70Row225 : TripleComponentParentRow :=
  tripleRow 2945 2913 83 40 149 83 24 81
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

def tttLargeFiber70Row226 : TripleComponentParentRow :=
  tripleRow 2946 2914 83 40 150 83 24 82
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row227 : TripleComponentParentRow :=
  tripleRow 2947 2944 83 40 151 83 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row228 : TripleComponentParentRow :=
  tripleRow 2948 2944 83 40 164 83 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row229 : TripleComponentParentRow :=
  tripleRow 2949 2945 83 40 165 83 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row230 : TripleComponentParentRow :=
  tripleRow 2950 2918 83 40 166 83 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row231 : TripleComponentParentRow :=
  tripleRow 2951 2919 83 40 167 83 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row232 : TripleComponentParentRow :=
  tripleRow 2952 2920 83 41 156 83 25 88
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

def tttLargeFiber70Row233 : TripleComponentParentRow :=
  tripleRow 2953 2921 83 41 157 83 25 89
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

def tttLargeFiber70Row234 : TripleComponentParentRow :=
  tripleRow 2954 2922 83 41 158 83 25 90
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row235 : TripleComponentParentRow :=
  tripleRow 2955 2952 83 41 159 83 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row236 : TripleComponentParentRow :=
  tripleRow 2956 2952 83 41 172 83 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row237 : TripleComponentParentRow :=
  tripleRow 2957 2953 83 41 173 83 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row238 : TripleComponentParentRow :=
  tripleRow 2958 2926 83 41 174 83 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row239 : TripleComponentParentRow :=
  tripleRow 2959 2927 83 41 175 83 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row224
  , tttLargeFiber70Row225
  , tttLargeFiber70Row226
  , tttLargeFiber70Row227
  , tttLargeFiber70Row228
  , tttLargeFiber70Row229
  , tttLargeFiber70Row230
  , tttLargeFiber70Row231
  , tttLargeFiber70Row232
  , tttLargeFiber70Row233
  , tttLargeFiber70Row234
  , tttLargeFiber70Row235
  , tttLargeFiber70Row236
  , tttLargeFiber70Row237
  , tttLargeFiber70Row238
  , tttLargeFiber70Row239
  ]

def tttLargeFiber70Block3Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block3Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block3Chunk2ExpectedContains row.source &&
    tttLargeFiber70Block3Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber70Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber70Block3Chunk2Sources

theorem tttLargeFiber70Block3Chunk2SourcesCheck_ok :
    tttLargeFiber70Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber70Block3Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block3Chunk2RowValid
    (listGetD tttLargeFiber70Block3Chunk2Rows i default)

def tttLargeFiber70Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block3Chunk2Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block3Chunk2Sources 0 0 == 2944
      && tttLargeFiber70ParentOf 2944 == 2912
      && tttLargeFiber70ParentOf 2912 == 2784
      && tttLargeFiber70ParentOf 2784 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block3Chunk2Sources 1 0 == 2945
      && tttLargeFiber70ParentOf 2945 == 2913
      && tttLargeFiber70ParentOf 2913 == 2785
      && tttLargeFiber70ParentOf 2785 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block3Chunk2Sources 2 0 == 2946
      && tttLargeFiber70ParentOf 2946 == 2914
      && tttLargeFiber70ParentOf 2914 == 2786
      && tttLargeFiber70ParentOf 2786 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block3Chunk2Sources 3 0 == 2947
      && tttLargeFiber70ParentOf 2947 == 2944
      && tttLargeFiber70ParentOf 2944 == 2912
      && tttLargeFiber70ParentOf 2912 == 2784
      && tttLargeFiber70ParentOf 2784 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block3Chunk2Sources 4 0 == 2948
      && tttLargeFiber70ParentOf 2948 == 2944
      && tttLargeFiber70ParentOf 2944 == 2912
      && tttLargeFiber70ParentOf 2912 == 2784
      && tttLargeFiber70ParentOf 2784 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block3Chunk2Sources 5 0 == 2949
      && tttLargeFiber70ParentOf 2949 == 2945
      && tttLargeFiber70ParentOf 2945 == 2913
      && tttLargeFiber70ParentOf 2913 == 2785
      && tttLargeFiber70ParentOf 2785 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block3Chunk2Sources 6 0 == 2950
      && tttLargeFiber70ParentOf 2950 == 2918
      && tttLargeFiber70ParentOf 2918 == 2790
      && tttLargeFiber70ParentOf 2790 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block3Chunk2Sources 7 0 == 2951
      && tttLargeFiber70ParentOf 2951 == 2919
      && tttLargeFiber70ParentOf 2919 == 2791
      && tttLargeFiber70ParentOf 2791 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block3Chunk2Sources 8 0 == 2952
      && tttLargeFiber70ParentOf 2952 == 2920
      && tttLargeFiber70ParentOf 2920 == 2792
      && tttLargeFiber70ParentOf 2792 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block3Chunk2Sources 9 0 == 2953
      && tttLargeFiber70ParentOf 2953 == 2921
      && tttLargeFiber70ParentOf 2921 == 2793
      && tttLargeFiber70ParentOf 2793 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block3Chunk2Sources 10 0 == 2954
      && tttLargeFiber70ParentOf 2954 == 2922
      && tttLargeFiber70ParentOf 2922 == 2794
      && tttLargeFiber70ParentOf 2794 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block3Chunk2Sources 11 0 == 2955
      && tttLargeFiber70ParentOf 2955 == 2952
      && tttLargeFiber70ParentOf 2952 == 2920
      && tttLargeFiber70ParentOf 2920 == 2792
      && tttLargeFiber70ParentOf 2792 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block3Chunk2Sources 12 0 == 2956
      && tttLargeFiber70ParentOf 2956 == 2952
      && tttLargeFiber70ParentOf 2952 == 2920
      && tttLargeFiber70ParentOf 2920 == 2792
      && tttLargeFiber70ParentOf 2792 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block3Chunk2Sources 13 0 == 2957
      && tttLargeFiber70ParentOf 2957 == 2953
      && tttLargeFiber70ParentOf 2953 == 2921
      && tttLargeFiber70ParentOf 2921 == 2793
      && tttLargeFiber70ParentOf 2793 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block3Chunk2Sources 14 0 == 2958
      && tttLargeFiber70ParentOf 2958 == 2926
      && tttLargeFiber70ParentOf 2926 == 2798
      && tttLargeFiber70ParentOf 2798 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block3Chunk2Sources 15 0 == 2959
      && tttLargeFiber70ParentOf 2959 == 2927
      && tttLargeFiber70ParentOf 2927 == 2799
      && tttLargeFiber70ParentOf 2799 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block3Chunk2Row_0_ok :
    tttLargeFiber70Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_1_ok :
    tttLargeFiber70Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_2_ok :
    tttLargeFiber70Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_3_ok :
    tttLargeFiber70Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_4_ok :
    tttLargeFiber70Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_5_ok :
    tttLargeFiber70Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_6_ok :
    tttLargeFiber70Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_7_ok :
    tttLargeFiber70Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_8_ok :
    tttLargeFiber70Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_9_ok :
    tttLargeFiber70Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_10_ok :
    tttLargeFiber70Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_11_ok :
    tttLargeFiber70Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_12_ok :
    tttLargeFiber70Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_13_ok :
    tttLargeFiber70Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_14_ok :
    tttLargeFiber70Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2Row_15_ok :
    tttLargeFiber70Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_0_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_1_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_2_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_3_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_4_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_5_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_6_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_7_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_8_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_9_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_10_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_11_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_12_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_13_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_14_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentMap_15_ok :
    tttLargeFiber70Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_0_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_1_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_2_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_3_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_4_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_5_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_6_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_7_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_8_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_9_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_10_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_11_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_12_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_13_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_14_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block3Chunk2ParentPath_15_ok :
    tttLargeFiber70Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber70Block3Chunk2RowCheck 0
    && tttLargeFiber70Block3Chunk2RowCheck 1
    && tttLargeFiber70Block3Chunk2RowCheck 2
    && tttLargeFiber70Block3Chunk2RowCheck 3
    && tttLargeFiber70Block3Chunk2RowCheck 4
    && tttLargeFiber70Block3Chunk2RowCheck 5
    && tttLargeFiber70Block3Chunk2RowCheck 6
    && tttLargeFiber70Block3Chunk2RowCheck 7
    && tttLargeFiber70Block3Chunk2RowCheck 8
    && tttLargeFiber70Block3Chunk2RowCheck 9
    && tttLargeFiber70Block3Chunk2RowCheck 10
    && tttLargeFiber70Block3Chunk2RowCheck 11
    && tttLargeFiber70Block3Chunk2RowCheck 12
    && tttLargeFiber70Block3Chunk2RowCheck 13
    && tttLargeFiber70Block3Chunk2RowCheck 14
    && tttLargeFiber70Block3Chunk2RowCheck 15

theorem tttLargeFiber70Block3Chunk2RowsAudit_ok :
    tttLargeFiber70Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber70Block3Chunk2RowsAudit,
    tttLargeFiber70Block3Chunk2Row_0_ok,
    tttLargeFiber70Block3Chunk2Row_1_ok,
    tttLargeFiber70Block3Chunk2Row_2_ok,
    tttLargeFiber70Block3Chunk2Row_3_ok,
    tttLargeFiber70Block3Chunk2Row_4_ok,
    tttLargeFiber70Block3Chunk2Row_5_ok,
    tttLargeFiber70Block3Chunk2Row_6_ok,
    tttLargeFiber70Block3Chunk2Row_7_ok,
    tttLargeFiber70Block3Chunk2Row_8_ok,
    tttLargeFiber70Block3Chunk2Row_9_ok,
    tttLargeFiber70Block3Chunk2Row_10_ok,
    tttLargeFiber70Block3Chunk2Row_11_ok,
    tttLargeFiber70Block3Chunk2Row_12_ok,
    tttLargeFiber70Block3Chunk2Row_13_ok,
    tttLargeFiber70Block3Chunk2Row_14_ok,
    tttLargeFiber70Block3Chunk2Row_15_ok]

def tttLargeFiber70Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber70Block3Chunk2ParentMapCheck 0
    && tttLargeFiber70Block3Chunk2ParentMapCheck 1
    && tttLargeFiber70Block3Chunk2ParentMapCheck 2
    && tttLargeFiber70Block3Chunk2ParentMapCheck 3
    && tttLargeFiber70Block3Chunk2ParentMapCheck 4
    && tttLargeFiber70Block3Chunk2ParentMapCheck 5
    && tttLargeFiber70Block3Chunk2ParentMapCheck 6
    && tttLargeFiber70Block3Chunk2ParentMapCheck 7
    && tttLargeFiber70Block3Chunk2ParentMapCheck 8
    && tttLargeFiber70Block3Chunk2ParentMapCheck 9
    && tttLargeFiber70Block3Chunk2ParentMapCheck 10
    && tttLargeFiber70Block3Chunk2ParentMapCheck 11
    && tttLargeFiber70Block3Chunk2ParentMapCheck 12
    && tttLargeFiber70Block3Chunk2ParentMapCheck 13
    && tttLargeFiber70Block3Chunk2ParentMapCheck 14
    && tttLargeFiber70Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber70Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber70Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber70Block3Chunk2ParentMapAudit,
    tttLargeFiber70Block3Chunk2ParentMap_0_ok,
    tttLargeFiber70Block3Chunk2ParentMap_1_ok,
    tttLargeFiber70Block3Chunk2ParentMap_2_ok,
    tttLargeFiber70Block3Chunk2ParentMap_3_ok,
    tttLargeFiber70Block3Chunk2ParentMap_4_ok,
    tttLargeFiber70Block3Chunk2ParentMap_5_ok,
    tttLargeFiber70Block3Chunk2ParentMap_6_ok,
    tttLargeFiber70Block3Chunk2ParentMap_7_ok,
    tttLargeFiber70Block3Chunk2ParentMap_8_ok,
    tttLargeFiber70Block3Chunk2ParentMap_9_ok,
    tttLargeFiber70Block3Chunk2ParentMap_10_ok,
    tttLargeFiber70Block3Chunk2ParentMap_11_ok,
    tttLargeFiber70Block3Chunk2ParentMap_12_ok,
    tttLargeFiber70Block3Chunk2ParentMap_13_ok,
    tttLargeFiber70Block3Chunk2ParentMap_14_ok,
    tttLargeFiber70Block3Chunk2ParentMap_15_ok]

def tttLargeFiber70Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber70Block3Chunk2ParentPathCheck 0
    && tttLargeFiber70Block3Chunk2ParentPathCheck 1
    && tttLargeFiber70Block3Chunk2ParentPathCheck 2
    && tttLargeFiber70Block3Chunk2ParentPathCheck 3
    && tttLargeFiber70Block3Chunk2ParentPathCheck 4
    && tttLargeFiber70Block3Chunk2ParentPathCheck 5
    && tttLargeFiber70Block3Chunk2ParentPathCheck 6
    && tttLargeFiber70Block3Chunk2ParentPathCheck 7
    && tttLargeFiber70Block3Chunk2ParentPathCheck 8
    && tttLargeFiber70Block3Chunk2ParentPathCheck 9
    && tttLargeFiber70Block3Chunk2ParentPathCheck 10
    && tttLargeFiber70Block3Chunk2ParentPathCheck 11
    && tttLargeFiber70Block3Chunk2ParentPathCheck 12
    && tttLargeFiber70Block3Chunk2ParentPathCheck 13
    && tttLargeFiber70Block3Chunk2ParentPathCheck 14
    && tttLargeFiber70Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber70Block3Chunk2ParentsAudit_ok :
    tttLargeFiber70Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber70Block3Chunk2ParentsAudit,
    tttLargeFiber70Block3Chunk2ParentPath_0_ok,
    tttLargeFiber70Block3Chunk2ParentPath_1_ok,
    tttLargeFiber70Block3Chunk2ParentPath_2_ok,
    tttLargeFiber70Block3Chunk2ParentPath_3_ok,
    tttLargeFiber70Block3Chunk2ParentPath_4_ok,
    tttLargeFiber70Block3Chunk2ParentPath_5_ok,
    tttLargeFiber70Block3Chunk2ParentPath_6_ok,
    tttLargeFiber70Block3Chunk2ParentPath_7_ok,
    tttLargeFiber70Block3Chunk2ParentPath_8_ok,
    tttLargeFiber70Block3Chunk2ParentPath_9_ok,
    tttLargeFiber70Block3Chunk2ParentPath_10_ok,
    tttLargeFiber70Block3Chunk2ParentPath_11_ok,
    tttLargeFiber70Block3Chunk2ParentPath_12_ok,
    tttLargeFiber70Block3Chunk2ParentPath_13_ok,
    tttLargeFiber70Block3Chunk2ParentPath_14_ok,
    tttLargeFiber70Block3Chunk2ParentPath_15_ok]

def tttLargeFiber70Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block3Chunk2SourcesCheck &&
    tttLargeFiber70Block3Chunk2RowsAudit &&
    tttLargeFiber70Block3Chunk2ParentMapAudit &&
    tttLargeFiber70Block3Chunk2ParentsAudit

theorem tttLargeFiber70Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber70Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block3Chunk2SourcesCheck_ok,
    tttLargeFiber70Block3Chunk2RowsAudit_ok,
    tttLargeFiber70Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber70Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
