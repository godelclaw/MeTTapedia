import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 2 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block2Chunk2Sources : List Nat :=
  [   2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887,
   2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]

def tttLargeFiber70Row160 : TripleComponentParentRow :=
  tripleRow 2880 2848 82 32 148 82 16 80
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

def tttLargeFiber70Row161 : TripleComponentParentRow :=
  tripleRow 2881 2849 82 32 149 82 16 81
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

def tttLargeFiber70Row162 : TripleComponentParentRow :=
  tripleRow 2882 2850 82 32 150 82 16 82
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

def tttLargeFiber70Row163 : TripleComponentParentRow :=
  tripleRow 2883 2880 82 32 151 82 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row164 : TripleComponentParentRow :=
  tripleRow 2884 2880 82 32 164 82 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row165 : TripleComponentParentRow :=
  tripleRow 2885 2881 82 32 165 82 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row166 : TripleComponentParentRow :=
  tripleRow 2886 2854 82 32 166 82 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row167 : TripleComponentParentRow :=
  tripleRow 2887 2855 82 32 167 82 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row168 : TripleComponentParentRow :=
  tripleRow 2888 2856 82 33 156 82 17 88
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

def tttLargeFiber70Row169 : TripleComponentParentRow :=
  tripleRow 2889 2857 82 33 157 82 17 89
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

def tttLargeFiber70Row170 : TripleComponentParentRow :=
  tripleRow 2890 2858 82 33 158 82 17 90
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

def tttLargeFiber70Row171 : TripleComponentParentRow :=
  tripleRow 2891 2888 82 33 159 82 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row172 : TripleComponentParentRow :=
  tripleRow 2892 2888 82 33 172 82 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row173 : TripleComponentParentRow :=
  tripleRow 2893 2889 82 33 173 82 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row174 : TripleComponentParentRow :=
  tripleRow 2894 2862 82 33 174 82 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row175 : TripleComponentParentRow :=
  tripleRow 2895 2863 82 33 175 82 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row160
  , tttLargeFiber70Row161
  , tttLargeFiber70Row162
  , tttLargeFiber70Row163
  , tttLargeFiber70Row164
  , tttLargeFiber70Row165
  , tttLargeFiber70Row166
  , tttLargeFiber70Row167
  , tttLargeFiber70Row168
  , tttLargeFiber70Row169
  , tttLargeFiber70Row170
  , tttLargeFiber70Row171
  , tttLargeFiber70Row172
  , tttLargeFiber70Row173
  , tttLargeFiber70Row174
  , tttLargeFiber70Row175
  ]

def tttLargeFiber70Block2Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block2Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block2Chunk2ExpectedContains row.source &&
    tttLargeFiber70Block2Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber70Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber70Block2Chunk2Sources

theorem tttLargeFiber70Block2Chunk2SourcesCheck_ok :
    tttLargeFiber70Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber70Block2Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block2Chunk2RowValid
    (listGetD tttLargeFiber70Block2Chunk2Rows i default)

def tttLargeFiber70Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block2Chunk2Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block2Chunk2Sources 0 0 == 2880
      && tttLargeFiber70ParentOf 2880 == 2848
      && tttLargeFiber70ParentOf 2848 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block2Chunk2Sources 1 0 == 2881
      && tttLargeFiber70ParentOf 2881 == 2849
      && tttLargeFiber70ParentOf 2849 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block2Chunk2Sources 2 0 == 2882
      && tttLargeFiber70ParentOf 2882 == 2850
      && tttLargeFiber70ParentOf 2850 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block2Chunk2Sources 3 0 == 2883
      && tttLargeFiber70ParentOf 2883 == 2880
      && tttLargeFiber70ParentOf 2880 == 2848
      && tttLargeFiber70ParentOf 2848 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block2Chunk2Sources 4 0 == 2884
      && tttLargeFiber70ParentOf 2884 == 2880
      && tttLargeFiber70ParentOf 2880 == 2848
      && tttLargeFiber70ParentOf 2848 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block2Chunk2Sources 5 0 == 2885
      && tttLargeFiber70ParentOf 2885 == 2881
      && tttLargeFiber70ParentOf 2881 == 2849
      && tttLargeFiber70ParentOf 2849 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block2Chunk2Sources 6 0 == 2886
      && tttLargeFiber70ParentOf 2886 == 2854
      && tttLargeFiber70ParentOf 2854 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block2Chunk2Sources 7 0 == 2887
      && tttLargeFiber70ParentOf 2887 == 2855
      && tttLargeFiber70ParentOf 2855 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block2Chunk2Sources 8 0 == 2888
      && tttLargeFiber70ParentOf 2888 == 2856
      && tttLargeFiber70ParentOf 2856 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block2Chunk2Sources 9 0 == 2889
      && tttLargeFiber70ParentOf 2889 == 2857
      && tttLargeFiber70ParentOf 2857 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block2Chunk2Sources 10 0 == 2890
      && tttLargeFiber70ParentOf 2890 == 2858
      && tttLargeFiber70ParentOf 2858 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block2Chunk2Sources 11 0 == 2891
      && tttLargeFiber70ParentOf 2891 == 2888
      && tttLargeFiber70ParentOf 2888 == 2856
      && tttLargeFiber70ParentOf 2856 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block2Chunk2Sources 12 0 == 2892
      && tttLargeFiber70ParentOf 2892 == 2888
      && tttLargeFiber70ParentOf 2888 == 2856
      && tttLargeFiber70ParentOf 2856 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block2Chunk2Sources 13 0 == 2893
      && tttLargeFiber70ParentOf 2893 == 2889
      && tttLargeFiber70ParentOf 2889 == 2857
      && tttLargeFiber70ParentOf 2857 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block2Chunk2Sources 14 0 == 2894
      && tttLargeFiber70ParentOf 2894 == 2862
      && tttLargeFiber70ParentOf 2862 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block2Chunk2Sources 15 0 == 2895
      && tttLargeFiber70ParentOf 2895 == 2863
      && tttLargeFiber70ParentOf 2863 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block2Chunk2Row_0_ok :
    tttLargeFiber70Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_1_ok :
    tttLargeFiber70Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_2_ok :
    tttLargeFiber70Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_3_ok :
    tttLargeFiber70Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_4_ok :
    tttLargeFiber70Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_5_ok :
    tttLargeFiber70Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_6_ok :
    tttLargeFiber70Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_7_ok :
    tttLargeFiber70Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_8_ok :
    tttLargeFiber70Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_9_ok :
    tttLargeFiber70Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_10_ok :
    tttLargeFiber70Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_11_ok :
    tttLargeFiber70Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_12_ok :
    tttLargeFiber70Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_13_ok :
    tttLargeFiber70Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_14_ok :
    tttLargeFiber70Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2Row_15_ok :
    tttLargeFiber70Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_0_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_1_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_2_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_3_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_4_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_5_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_6_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_7_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_8_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_9_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_10_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_11_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_12_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_13_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_14_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentMap_15_ok :
    tttLargeFiber70Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_0_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_1_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_2_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_3_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_4_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_5_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_6_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_7_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_8_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_9_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_10_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_11_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_12_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_13_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_14_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block2Chunk2ParentPath_15_ok :
    tttLargeFiber70Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber70Block2Chunk2RowCheck 0
    && tttLargeFiber70Block2Chunk2RowCheck 1
    && tttLargeFiber70Block2Chunk2RowCheck 2
    && tttLargeFiber70Block2Chunk2RowCheck 3
    && tttLargeFiber70Block2Chunk2RowCheck 4
    && tttLargeFiber70Block2Chunk2RowCheck 5
    && tttLargeFiber70Block2Chunk2RowCheck 6
    && tttLargeFiber70Block2Chunk2RowCheck 7
    && tttLargeFiber70Block2Chunk2RowCheck 8
    && tttLargeFiber70Block2Chunk2RowCheck 9
    && tttLargeFiber70Block2Chunk2RowCheck 10
    && tttLargeFiber70Block2Chunk2RowCheck 11
    && tttLargeFiber70Block2Chunk2RowCheck 12
    && tttLargeFiber70Block2Chunk2RowCheck 13
    && tttLargeFiber70Block2Chunk2RowCheck 14
    && tttLargeFiber70Block2Chunk2RowCheck 15

theorem tttLargeFiber70Block2Chunk2RowsAudit_ok :
    tttLargeFiber70Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber70Block2Chunk2RowsAudit,
    tttLargeFiber70Block2Chunk2Row_0_ok,
    tttLargeFiber70Block2Chunk2Row_1_ok,
    tttLargeFiber70Block2Chunk2Row_2_ok,
    tttLargeFiber70Block2Chunk2Row_3_ok,
    tttLargeFiber70Block2Chunk2Row_4_ok,
    tttLargeFiber70Block2Chunk2Row_5_ok,
    tttLargeFiber70Block2Chunk2Row_6_ok,
    tttLargeFiber70Block2Chunk2Row_7_ok,
    tttLargeFiber70Block2Chunk2Row_8_ok,
    tttLargeFiber70Block2Chunk2Row_9_ok,
    tttLargeFiber70Block2Chunk2Row_10_ok,
    tttLargeFiber70Block2Chunk2Row_11_ok,
    tttLargeFiber70Block2Chunk2Row_12_ok,
    tttLargeFiber70Block2Chunk2Row_13_ok,
    tttLargeFiber70Block2Chunk2Row_14_ok,
    tttLargeFiber70Block2Chunk2Row_15_ok]

def tttLargeFiber70Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber70Block2Chunk2ParentMapCheck 0
    && tttLargeFiber70Block2Chunk2ParentMapCheck 1
    && tttLargeFiber70Block2Chunk2ParentMapCheck 2
    && tttLargeFiber70Block2Chunk2ParentMapCheck 3
    && tttLargeFiber70Block2Chunk2ParentMapCheck 4
    && tttLargeFiber70Block2Chunk2ParentMapCheck 5
    && tttLargeFiber70Block2Chunk2ParentMapCheck 6
    && tttLargeFiber70Block2Chunk2ParentMapCheck 7
    && tttLargeFiber70Block2Chunk2ParentMapCheck 8
    && tttLargeFiber70Block2Chunk2ParentMapCheck 9
    && tttLargeFiber70Block2Chunk2ParentMapCheck 10
    && tttLargeFiber70Block2Chunk2ParentMapCheck 11
    && tttLargeFiber70Block2Chunk2ParentMapCheck 12
    && tttLargeFiber70Block2Chunk2ParentMapCheck 13
    && tttLargeFiber70Block2Chunk2ParentMapCheck 14
    && tttLargeFiber70Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber70Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber70Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber70Block2Chunk2ParentMapAudit,
    tttLargeFiber70Block2Chunk2ParentMap_0_ok,
    tttLargeFiber70Block2Chunk2ParentMap_1_ok,
    tttLargeFiber70Block2Chunk2ParentMap_2_ok,
    tttLargeFiber70Block2Chunk2ParentMap_3_ok,
    tttLargeFiber70Block2Chunk2ParentMap_4_ok,
    tttLargeFiber70Block2Chunk2ParentMap_5_ok,
    tttLargeFiber70Block2Chunk2ParentMap_6_ok,
    tttLargeFiber70Block2Chunk2ParentMap_7_ok,
    tttLargeFiber70Block2Chunk2ParentMap_8_ok,
    tttLargeFiber70Block2Chunk2ParentMap_9_ok,
    tttLargeFiber70Block2Chunk2ParentMap_10_ok,
    tttLargeFiber70Block2Chunk2ParentMap_11_ok,
    tttLargeFiber70Block2Chunk2ParentMap_12_ok,
    tttLargeFiber70Block2Chunk2ParentMap_13_ok,
    tttLargeFiber70Block2Chunk2ParentMap_14_ok,
    tttLargeFiber70Block2Chunk2ParentMap_15_ok]

def tttLargeFiber70Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber70Block2Chunk2ParentPathCheck 0
    && tttLargeFiber70Block2Chunk2ParentPathCheck 1
    && tttLargeFiber70Block2Chunk2ParentPathCheck 2
    && tttLargeFiber70Block2Chunk2ParentPathCheck 3
    && tttLargeFiber70Block2Chunk2ParentPathCheck 4
    && tttLargeFiber70Block2Chunk2ParentPathCheck 5
    && tttLargeFiber70Block2Chunk2ParentPathCheck 6
    && tttLargeFiber70Block2Chunk2ParentPathCheck 7
    && tttLargeFiber70Block2Chunk2ParentPathCheck 8
    && tttLargeFiber70Block2Chunk2ParentPathCheck 9
    && tttLargeFiber70Block2Chunk2ParentPathCheck 10
    && tttLargeFiber70Block2Chunk2ParentPathCheck 11
    && tttLargeFiber70Block2Chunk2ParentPathCheck 12
    && tttLargeFiber70Block2Chunk2ParentPathCheck 13
    && tttLargeFiber70Block2Chunk2ParentPathCheck 14
    && tttLargeFiber70Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber70Block2Chunk2ParentsAudit_ok :
    tttLargeFiber70Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber70Block2Chunk2ParentsAudit,
    tttLargeFiber70Block2Chunk2ParentPath_0_ok,
    tttLargeFiber70Block2Chunk2ParentPath_1_ok,
    tttLargeFiber70Block2Chunk2ParentPath_2_ok,
    tttLargeFiber70Block2Chunk2ParentPath_3_ok,
    tttLargeFiber70Block2Chunk2ParentPath_4_ok,
    tttLargeFiber70Block2Chunk2ParentPath_5_ok,
    tttLargeFiber70Block2Chunk2ParentPath_6_ok,
    tttLargeFiber70Block2Chunk2ParentPath_7_ok,
    tttLargeFiber70Block2Chunk2ParentPath_8_ok,
    tttLargeFiber70Block2Chunk2ParentPath_9_ok,
    tttLargeFiber70Block2Chunk2ParentPath_10_ok,
    tttLargeFiber70Block2Chunk2ParentPath_11_ok,
    tttLargeFiber70Block2Chunk2ParentPath_12_ok,
    tttLargeFiber70Block2Chunk2ParentPath_13_ok,
    tttLargeFiber70Block2Chunk2ParentPath_14_ok,
    tttLargeFiber70Block2Chunk2ParentPath_15_ok]

def tttLargeFiber70Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block2Chunk2SourcesCheck &&
    tttLargeFiber70Block2Chunk2RowsAudit &&
    tttLargeFiber70Block2Chunk2ParentMapAudit &&
    tttLargeFiber70Block2Chunk2ParentsAudit

theorem tttLargeFiber70Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber70Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block2Chunk2SourcesCheck_ok,
    tttLargeFiber70Block2Chunk2RowsAudit_ok,
    tttLargeFiber70Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber70Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
