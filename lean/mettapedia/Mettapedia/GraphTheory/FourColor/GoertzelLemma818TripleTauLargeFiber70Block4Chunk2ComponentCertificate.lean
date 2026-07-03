import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 4 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block4Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block4Chunk2Sources : List Nat :=
  [   3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319,
   3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327]

def tttLargeFiber70Row288 : TripleComponentParentRow :=
  tripleRow 3312 3328 100 180 132 100 182 64
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row289 : TripleComponentParentRow :=
  tripleRow 3313 3329 100 180 133 100 182 65
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row290 : TripleComponentParentRow :=
  tripleRow 3314 2870 100 180 134 82 18 34
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row291 : TripleComponentParentRow :=
  tripleRow 3315 2871 100 180 135 82 18 35
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber70Row292 : TripleComponentParentRow :=
  tripleRow 3316 2866 100 180 180 82 18 18
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row293 : TripleComponentParentRow :=
  tripleRow 3317 3319 100 180 181 100 180 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row294 : TripleComponentParentRow :=
  tripleRow 3318 2865 100 180 182 82 18 17
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row295 : TripleComponentParentRow :=
  tripleRow 3319 2864 100 180 183 82 18 16
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row296 : TripleComponentParentRow :=
  tripleRow 3320 3336 100 181 140 100 183 72
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row297 : TripleComponentParentRow :=
  tripleRow 3321 3337 100 181 141 100 183 73
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row298 : TripleComponentParentRow :=
  tripleRow 3322 3338 100 181 142 100 183 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row299 : TripleComponentParentRow :=
  tripleRow 3323 3320 100 181 143 100 181 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row300 : TripleComponentParentRow :=
  tripleRow 3324 3320 100 181 188 100 181 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row301 : TripleComponentParentRow :=
  tripleRow 3325 3321 100 181 189 100 181 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row302 : TripleComponentParentRow :=
  tripleRow 3326 3342 100 181 190 100 183 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber70Row303 : TripleComponentParentRow :=
  tripleRow 3327 3343 100 181 191 100 183 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber70Block4Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row288
  , tttLargeFiber70Row289
  , tttLargeFiber70Row290
  , tttLargeFiber70Row291
  , tttLargeFiber70Row292
  , tttLargeFiber70Row293
  , tttLargeFiber70Row294
  , tttLargeFiber70Row295
  , tttLargeFiber70Row296
  , tttLargeFiber70Row297
  , tttLargeFiber70Row298
  , tttLargeFiber70Row299
  , tttLargeFiber70Row300
  , tttLargeFiber70Row301
  , tttLargeFiber70Row302
  , tttLargeFiber70Row303
  ]

def tttLargeFiber70Block4Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block4Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block4Chunk2ExpectedContains row.source &&
    tttLargeFiber70Block4Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block4Chunk2SourcesCheck : Bool :=
  (tttLargeFiber70Block4Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber70Block4Chunk2Sources

theorem tttLargeFiber70Block4Chunk2SourcesCheck_ok :
    tttLargeFiber70Block4Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber70Block4Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block4Chunk2RowValid
    (listGetD tttLargeFiber70Block4Chunk2Rows i default)

def tttLargeFiber70Block4Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block4Chunk2Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block4Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block4Chunk2Sources 0 0 == 3312
      && tttLargeFiber70ParentOf 3312 == 3328
      && tttLargeFiber70ParentOf 3328 == 2856
      && tttLargeFiber70ParentOf 2856 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block4Chunk2Sources 1 0 == 3313
      && tttLargeFiber70ParentOf 3313 == 3329
      && tttLargeFiber70ParentOf 3329 == 2857
      && tttLargeFiber70ParentOf 2857 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block4Chunk2Sources 2 0 == 3314
      && tttLargeFiber70ParentOf 3314 == 2870
      && tttLargeFiber70ParentOf 2870 == 2742
      && tttLargeFiber70ParentOf 2742 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block4Chunk2Sources 3 0 == 3315
      && tttLargeFiber70ParentOf 3315 == 2871
      && tttLargeFiber70ParentOf 2871 == 2743
      && tttLargeFiber70ParentOf 2743 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block4Chunk2Sources 4 0 == 3316
      && tttLargeFiber70ParentOf 3316 == 2866
      && tttLargeFiber70ParentOf 2866 == 2738
      && tttLargeFiber70ParentOf 2738 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block4Chunk2Sources 5 0 == 3317
      && tttLargeFiber70ParentOf 3317 == 3319
      && tttLargeFiber70ParentOf 3319 == 2864
      && tttLargeFiber70ParentOf 2864 == 2736
      && tttLargeFiber70ParentOf 2736 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block4Chunk2Sources 6 0 == 3318
      && tttLargeFiber70ParentOf 3318 == 2865
      && tttLargeFiber70ParentOf 2865 == 2737
      && tttLargeFiber70ParentOf 2737 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block4Chunk2Sources 7 0 == 3319
      && tttLargeFiber70ParentOf 3319 == 2864
      && tttLargeFiber70ParentOf 2864 == 2736
      && tttLargeFiber70ParentOf 2736 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block4Chunk2Sources 8 0 == 3320
      && tttLargeFiber70ParentOf 3320 == 3336
      && tttLargeFiber70ParentOf 3336 == 2848
      && tttLargeFiber70ParentOf 2848 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block4Chunk2Sources 9 0 == 3321
      && tttLargeFiber70ParentOf 3321 == 3337
      && tttLargeFiber70ParentOf 3337 == 2849
      && tttLargeFiber70ParentOf 2849 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block4Chunk2Sources 10 0 == 3322
      && tttLargeFiber70ParentOf 3322 == 3338
      && tttLargeFiber70ParentOf 3338 == 2850
      && tttLargeFiber70ParentOf 2850 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block4Chunk2Sources 11 0 == 3323
      && tttLargeFiber70ParentOf 3323 == 3320
      && tttLargeFiber70ParentOf 3320 == 3336
      && tttLargeFiber70ParentOf 3336 == 2848
      && tttLargeFiber70ParentOf 2848 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block4Chunk2Sources 12 0 == 3324
      && tttLargeFiber70ParentOf 3324 == 3320
      && tttLargeFiber70ParentOf 3320 == 3336
      && tttLargeFiber70ParentOf 3336 == 2848
      && tttLargeFiber70ParentOf 2848 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block4Chunk2Sources 13 0 == 3325
      && tttLargeFiber70ParentOf 3325 == 3321
      && tttLargeFiber70ParentOf 3321 == 3337
      && tttLargeFiber70ParentOf 3337 == 2849
      && tttLargeFiber70ParentOf 2849 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block4Chunk2Sources 14 0 == 3326
      && tttLargeFiber70ParentOf 3326 == 3342
      && tttLargeFiber70ParentOf 3342 == 2854
      && tttLargeFiber70ParentOf 2854 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block4Chunk2Sources 15 0 == 3327
      && tttLargeFiber70ParentOf 3327 == 3343
      && tttLargeFiber70ParentOf 3343 == 2855
      && tttLargeFiber70ParentOf 2855 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block4Chunk2Row_0_ok :
    tttLargeFiber70Block4Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_1_ok :
    tttLargeFiber70Block4Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_2_ok :
    tttLargeFiber70Block4Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_3_ok :
    tttLargeFiber70Block4Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_4_ok :
    tttLargeFiber70Block4Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_5_ok :
    tttLargeFiber70Block4Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_6_ok :
    tttLargeFiber70Block4Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_7_ok :
    tttLargeFiber70Block4Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_8_ok :
    tttLargeFiber70Block4Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_9_ok :
    tttLargeFiber70Block4Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_10_ok :
    tttLargeFiber70Block4Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_11_ok :
    tttLargeFiber70Block4Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_12_ok :
    tttLargeFiber70Block4Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_13_ok :
    tttLargeFiber70Block4Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_14_ok :
    tttLargeFiber70Block4Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2Row_15_ok :
    tttLargeFiber70Block4Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_0_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_1_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_2_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_3_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_4_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_5_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_6_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_7_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_8_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_9_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_10_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_11_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_12_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_13_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_14_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentMap_15_ok :
    tttLargeFiber70Block4Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_0_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_1_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_2_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_3_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_4_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_5_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_6_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_7_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_8_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_9_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_10_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_11_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_12_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_13_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_14_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block4Chunk2ParentPath_15_ok :
    tttLargeFiber70Block4Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block4Chunk2RowsAudit : Bool :=
  tttLargeFiber70Block4Chunk2RowCheck 0
    && tttLargeFiber70Block4Chunk2RowCheck 1
    && tttLargeFiber70Block4Chunk2RowCheck 2
    && tttLargeFiber70Block4Chunk2RowCheck 3
    && tttLargeFiber70Block4Chunk2RowCheck 4
    && tttLargeFiber70Block4Chunk2RowCheck 5
    && tttLargeFiber70Block4Chunk2RowCheck 6
    && tttLargeFiber70Block4Chunk2RowCheck 7
    && tttLargeFiber70Block4Chunk2RowCheck 8
    && tttLargeFiber70Block4Chunk2RowCheck 9
    && tttLargeFiber70Block4Chunk2RowCheck 10
    && tttLargeFiber70Block4Chunk2RowCheck 11
    && tttLargeFiber70Block4Chunk2RowCheck 12
    && tttLargeFiber70Block4Chunk2RowCheck 13
    && tttLargeFiber70Block4Chunk2RowCheck 14
    && tttLargeFiber70Block4Chunk2RowCheck 15

theorem tttLargeFiber70Block4Chunk2RowsAudit_ok :
    tttLargeFiber70Block4Chunk2RowsAudit = true := by
  simp [tttLargeFiber70Block4Chunk2RowsAudit,
    tttLargeFiber70Block4Chunk2Row_0_ok,
    tttLargeFiber70Block4Chunk2Row_1_ok,
    tttLargeFiber70Block4Chunk2Row_2_ok,
    tttLargeFiber70Block4Chunk2Row_3_ok,
    tttLargeFiber70Block4Chunk2Row_4_ok,
    tttLargeFiber70Block4Chunk2Row_5_ok,
    tttLargeFiber70Block4Chunk2Row_6_ok,
    tttLargeFiber70Block4Chunk2Row_7_ok,
    tttLargeFiber70Block4Chunk2Row_8_ok,
    tttLargeFiber70Block4Chunk2Row_9_ok,
    tttLargeFiber70Block4Chunk2Row_10_ok,
    tttLargeFiber70Block4Chunk2Row_11_ok,
    tttLargeFiber70Block4Chunk2Row_12_ok,
    tttLargeFiber70Block4Chunk2Row_13_ok,
    tttLargeFiber70Block4Chunk2Row_14_ok,
    tttLargeFiber70Block4Chunk2Row_15_ok]

def tttLargeFiber70Block4Chunk2ParentMapAudit : Bool :=
  tttLargeFiber70Block4Chunk2ParentMapCheck 0
    && tttLargeFiber70Block4Chunk2ParentMapCheck 1
    && tttLargeFiber70Block4Chunk2ParentMapCheck 2
    && tttLargeFiber70Block4Chunk2ParentMapCheck 3
    && tttLargeFiber70Block4Chunk2ParentMapCheck 4
    && tttLargeFiber70Block4Chunk2ParentMapCheck 5
    && tttLargeFiber70Block4Chunk2ParentMapCheck 6
    && tttLargeFiber70Block4Chunk2ParentMapCheck 7
    && tttLargeFiber70Block4Chunk2ParentMapCheck 8
    && tttLargeFiber70Block4Chunk2ParentMapCheck 9
    && tttLargeFiber70Block4Chunk2ParentMapCheck 10
    && tttLargeFiber70Block4Chunk2ParentMapCheck 11
    && tttLargeFiber70Block4Chunk2ParentMapCheck 12
    && tttLargeFiber70Block4Chunk2ParentMapCheck 13
    && tttLargeFiber70Block4Chunk2ParentMapCheck 14
    && tttLargeFiber70Block4Chunk2ParentMapCheck 15

theorem tttLargeFiber70Block4Chunk2ParentMapAudit_ok :
    tttLargeFiber70Block4Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber70Block4Chunk2ParentMapAudit,
    tttLargeFiber70Block4Chunk2ParentMap_0_ok,
    tttLargeFiber70Block4Chunk2ParentMap_1_ok,
    tttLargeFiber70Block4Chunk2ParentMap_2_ok,
    tttLargeFiber70Block4Chunk2ParentMap_3_ok,
    tttLargeFiber70Block4Chunk2ParentMap_4_ok,
    tttLargeFiber70Block4Chunk2ParentMap_5_ok,
    tttLargeFiber70Block4Chunk2ParentMap_6_ok,
    tttLargeFiber70Block4Chunk2ParentMap_7_ok,
    tttLargeFiber70Block4Chunk2ParentMap_8_ok,
    tttLargeFiber70Block4Chunk2ParentMap_9_ok,
    tttLargeFiber70Block4Chunk2ParentMap_10_ok,
    tttLargeFiber70Block4Chunk2ParentMap_11_ok,
    tttLargeFiber70Block4Chunk2ParentMap_12_ok,
    tttLargeFiber70Block4Chunk2ParentMap_13_ok,
    tttLargeFiber70Block4Chunk2ParentMap_14_ok,
    tttLargeFiber70Block4Chunk2ParentMap_15_ok]

def tttLargeFiber70Block4Chunk2ParentsAudit : Bool :=
  tttLargeFiber70Block4Chunk2ParentPathCheck 0
    && tttLargeFiber70Block4Chunk2ParentPathCheck 1
    && tttLargeFiber70Block4Chunk2ParentPathCheck 2
    && tttLargeFiber70Block4Chunk2ParentPathCheck 3
    && tttLargeFiber70Block4Chunk2ParentPathCheck 4
    && tttLargeFiber70Block4Chunk2ParentPathCheck 5
    && tttLargeFiber70Block4Chunk2ParentPathCheck 6
    && tttLargeFiber70Block4Chunk2ParentPathCheck 7
    && tttLargeFiber70Block4Chunk2ParentPathCheck 8
    && tttLargeFiber70Block4Chunk2ParentPathCheck 9
    && tttLargeFiber70Block4Chunk2ParentPathCheck 10
    && tttLargeFiber70Block4Chunk2ParentPathCheck 11
    && tttLargeFiber70Block4Chunk2ParentPathCheck 12
    && tttLargeFiber70Block4Chunk2ParentPathCheck 13
    && tttLargeFiber70Block4Chunk2ParentPathCheck 14
    && tttLargeFiber70Block4Chunk2ParentPathCheck 15

theorem tttLargeFiber70Block4Chunk2ParentsAudit_ok :
    tttLargeFiber70Block4Chunk2ParentsAudit = true := by
  simp [tttLargeFiber70Block4Chunk2ParentsAudit,
    tttLargeFiber70Block4Chunk2ParentPath_0_ok,
    tttLargeFiber70Block4Chunk2ParentPath_1_ok,
    tttLargeFiber70Block4Chunk2ParentPath_2_ok,
    tttLargeFiber70Block4Chunk2ParentPath_3_ok,
    tttLargeFiber70Block4Chunk2ParentPath_4_ok,
    tttLargeFiber70Block4Chunk2ParentPath_5_ok,
    tttLargeFiber70Block4Chunk2ParentPath_6_ok,
    tttLargeFiber70Block4Chunk2ParentPath_7_ok,
    tttLargeFiber70Block4Chunk2ParentPath_8_ok,
    tttLargeFiber70Block4Chunk2ParentPath_9_ok,
    tttLargeFiber70Block4Chunk2ParentPath_10_ok,
    tttLargeFiber70Block4Chunk2ParentPath_11_ok,
    tttLargeFiber70Block4Chunk2ParentPath_12_ok,
    tttLargeFiber70Block4Chunk2ParentPath_13_ok,
    tttLargeFiber70Block4Chunk2ParentPath_14_ok,
    tttLargeFiber70Block4Chunk2ParentPath_15_ok]

def tttLargeFiber70Block4Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block4Chunk2SourcesCheck &&
    tttLargeFiber70Block4Chunk2RowsAudit &&
    tttLargeFiber70Block4Chunk2ParentMapAudit &&
    tttLargeFiber70Block4Chunk2ParentsAudit

theorem tttLargeFiber70Block4Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber70Block4Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block4Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block4Chunk2SourcesCheck_ok,
    tttLargeFiber70Block4Chunk2RowsAudit_ok,
    tttLargeFiber70Block4Chunk2ParentMapAudit_ok,
    tttLargeFiber70Block4Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block4Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
