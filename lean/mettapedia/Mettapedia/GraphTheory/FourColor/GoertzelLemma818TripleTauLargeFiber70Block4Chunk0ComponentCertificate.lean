import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 4 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block4Chunk0Sources : List Nat :=
  [   3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287,
   3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295]

def tttLargeFiber70Row256 : TripleComponentParentRow :=
  tripleRow 3280 3408 100 132 148 102 64 80
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Row257 : TripleComponentParentRow :=
  tripleRow 3281 3409 100 132 149 102 64 81
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Row258 : TripleComponentParentRow :=
  tripleRow 3282 3410 100 132 150 102 64 82
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row259 : TripleComponentParentRow :=
  tripleRow 3283 3280 100 132 151 100 132 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row260 : TripleComponentParentRow :=
  tripleRow 3284 3280 100 132 164 100 132 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row261 : TripleComponentParentRow :=
  tripleRow 3285 3281 100 132 165 100 132 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row262 : TripleComponentParentRow :=
  tripleRow 3286 3414 100 132 166 102 64 102
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Row263 : TripleComponentParentRow :=
  tripleRow 3287 3415 100 132 167 102 64 103
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Row264 : TripleComponentParentRow :=
  tripleRow 3288 3416 100 133 156 102 65 88
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Row265 : TripleComponentParentRow :=
  tripleRow 3289 3417 100 133 157 102 65 89
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Row266 : TripleComponentParentRow :=
  tripleRow 3290 3418 100 133 158 102 65 90
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row267 : TripleComponentParentRow :=
  tripleRow 3291 3288 100 133 159 100 133 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row268 : TripleComponentParentRow :=
  tripleRow 3292 3288 100 133 172 100 133 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row269 : TripleComponentParentRow :=
  tripleRow 3293 3289 100 133 173 100 133 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row270 : TripleComponentParentRow :=
  tripleRow 3294 3422 100 133 174 102 65 110
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Row271 : TripleComponentParentRow :=
  tripleRow 3295 3423 100 133 175 102 65 111
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber70Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row256
  , tttLargeFiber70Row257
  , tttLargeFiber70Row258
  , tttLargeFiber70Row259
  , tttLargeFiber70Row260
  , tttLargeFiber70Row261
  , tttLargeFiber70Row262
  , tttLargeFiber70Row263
  , tttLargeFiber70Row264
  , tttLargeFiber70Row265
  , tttLargeFiber70Row266
  , tttLargeFiber70Row267
  , tttLargeFiber70Row268
  , tttLargeFiber70Row269
  , tttLargeFiber70Row270
  , tttLargeFiber70Row271
  ]

def tttLargeFiber70Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber70Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber70Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber70Block4Chunk0Sources

theorem tttLargeFiber70Block4Chunk0SourcesCheck_ok :
    tttLargeFiber70Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber70Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block4Chunk0RowValid
    (listGetD tttLargeFiber70Block4Chunk0Rows i default)

def tttLargeFiber70Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block4Chunk0Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block4Chunk0Sources 0 0 == 3280
      && tttLargeFiber70ParentOf 3280 == 3408
      && tttLargeFiber70ParentOf 3408 == 2784
      && tttLargeFiber70ParentOf 2784 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block4Chunk0Sources 1 0 == 3281
      && tttLargeFiber70ParentOf 3281 == 3409
      && tttLargeFiber70ParentOf 3409 == 2785
      && tttLargeFiber70ParentOf 2785 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block4Chunk0Sources 2 0 == 3282
      && tttLargeFiber70ParentOf 3282 == 3410
      && tttLargeFiber70ParentOf 3410 == 2786
      && tttLargeFiber70ParentOf 2786 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block4Chunk0Sources 3 0 == 3283
      && tttLargeFiber70ParentOf 3283 == 3280
      && tttLargeFiber70ParentOf 3280 == 3408
      && tttLargeFiber70ParentOf 3408 == 2784
      && tttLargeFiber70ParentOf 2784 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block4Chunk0Sources 4 0 == 3284
      && tttLargeFiber70ParentOf 3284 == 3280
      && tttLargeFiber70ParentOf 3280 == 3408
      && tttLargeFiber70ParentOf 3408 == 2784
      && tttLargeFiber70ParentOf 2784 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block4Chunk0Sources 5 0 == 3285
      && tttLargeFiber70ParentOf 3285 == 3281
      && tttLargeFiber70ParentOf 3281 == 3409
      && tttLargeFiber70ParentOf 3409 == 2785
      && tttLargeFiber70ParentOf 2785 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block4Chunk0Sources 6 0 == 3286
      && tttLargeFiber70ParentOf 3286 == 3414
      && tttLargeFiber70ParentOf 3414 == 2790
      && tttLargeFiber70ParentOf 2790 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block4Chunk0Sources 7 0 == 3287
      && tttLargeFiber70ParentOf 3287 == 3415
      && tttLargeFiber70ParentOf 3415 == 2791
      && tttLargeFiber70ParentOf 2791 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block4Chunk0Sources 8 0 == 3288
      && tttLargeFiber70ParentOf 3288 == 3416
      && tttLargeFiber70ParentOf 3416 == 2792
      && tttLargeFiber70ParentOf 2792 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (4 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block4Chunk0Sources 9 0 == 3289
      && tttLargeFiber70ParentOf 3289 == 3417
      && tttLargeFiber70ParentOf 3417 == 2793
      && tttLargeFiber70ParentOf 2793 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block4Chunk0Sources 10 0 == 3290
      && tttLargeFiber70ParentOf 3290 == 3418
      && tttLargeFiber70ParentOf 3418 == 2794
      && tttLargeFiber70ParentOf 2794 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block4Chunk0Sources 11 0 == 3291
      && tttLargeFiber70ParentOf 3291 == 3288
      && tttLargeFiber70ParentOf 3288 == 3416
      && tttLargeFiber70ParentOf 3416 == 2792
      && tttLargeFiber70ParentOf 2792 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block4Chunk0Sources 12 0 == 3292
      && tttLargeFiber70ParentOf 3292 == 3288
      && tttLargeFiber70ParentOf 3288 == 3416
      && tttLargeFiber70ParentOf 3416 == 2792
      && tttLargeFiber70ParentOf 2792 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block4Chunk0Sources 13 0 == 3293
      && tttLargeFiber70ParentOf 3293 == 3289
      && tttLargeFiber70ParentOf 3289 == 3417
      && tttLargeFiber70ParentOf 3417 == 2793
      && tttLargeFiber70ParentOf 2793 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block4Chunk0Sources 14 0 == 3294
      && tttLargeFiber70ParentOf 3294 == 3422
      && tttLargeFiber70ParentOf 3422 == 2798
      && tttLargeFiber70ParentOf 2798 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (6 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block4Chunk0Sources 15 0 == 3295
      && tttLargeFiber70ParentOf 3295 == 3423
      && tttLargeFiber70ParentOf 3423 == 2799
      && tttLargeFiber70ParentOf 2799 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (5 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block4Chunk0Row_0_ok :
    tttLargeFiber70Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_1_ok :
    tttLargeFiber70Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_2_ok :
    tttLargeFiber70Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_3_ok :
    tttLargeFiber70Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_4_ok :
    tttLargeFiber70Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_5_ok :
    tttLargeFiber70Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_6_ok :
    tttLargeFiber70Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_7_ok :
    tttLargeFiber70Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_8_ok :
    tttLargeFiber70Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_9_ok :
    tttLargeFiber70Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_10_ok :
    tttLargeFiber70Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_11_ok :
    tttLargeFiber70Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_12_ok :
    tttLargeFiber70Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_13_ok :
    tttLargeFiber70Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_14_ok :
    tttLargeFiber70Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0Row_15_ok :
    tttLargeFiber70Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_0_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_1_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_2_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_3_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_4_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_5_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_6_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_7_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_8_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_9_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_10_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_11_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_12_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_13_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_14_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentMap_15_ok :
    tttLargeFiber70Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_0_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_1_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_2_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_3_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_4_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_5_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_6_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_7_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_8_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_9_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_10_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_11_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_12_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_13_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_14_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block4Chunk0ParentPath_15_ok :
    tttLargeFiber70Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber70Block4Chunk0RowCheck 0
    && tttLargeFiber70Block4Chunk0RowCheck 1
    && tttLargeFiber70Block4Chunk0RowCheck 2
    && tttLargeFiber70Block4Chunk0RowCheck 3
    && tttLargeFiber70Block4Chunk0RowCheck 4
    && tttLargeFiber70Block4Chunk0RowCheck 5
    && tttLargeFiber70Block4Chunk0RowCheck 6
    && tttLargeFiber70Block4Chunk0RowCheck 7
    && tttLargeFiber70Block4Chunk0RowCheck 8
    && tttLargeFiber70Block4Chunk0RowCheck 9
    && tttLargeFiber70Block4Chunk0RowCheck 10
    && tttLargeFiber70Block4Chunk0RowCheck 11
    && tttLargeFiber70Block4Chunk0RowCheck 12
    && tttLargeFiber70Block4Chunk0RowCheck 13
    && tttLargeFiber70Block4Chunk0RowCheck 14
    && tttLargeFiber70Block4Chunk0RowCheck 15

theorem tttLargeFiber70Block4Chunk0RowsAudit_ok :
    tttLargeFiber70Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber70Block4Chunk0RowsAudit,
    tttLargeFiber70Block4Chunk0Row_0_ok,
    tttLargeFiber70Block4Chunk0Row_1_ok,
    tttLargeFiber70Block4Chunk0Row_2_ok,
    tttLargeFiber70Block4Chunk0Row_3_ok,
    tttLargeFiber70Block4Chunk0Row_4_ok,
    tttLargeFiber70Block4Chunk0Row_5_ok,
    tttLargeFiber70Block4Chunk0Row_6_ok,
    tttLargeFiber70Block4Chunk0Row_7_ok,
    tttLargeFiber70Block4Chunk0Row_8_ok,
    tttLargeFiber70Block4Chunk0Row_9_ok,
    tttLargeFiber70Block4Chunk0Row_10_ok,
    tttLargeFiber70Block4Chunk0Row_11_ok,
    tttLargeFiber70Block4Chunk0Row_12_ok,
    tttLargeFiber70Block4Chunk0Row_13_ok,
    tttLargeFiber70Block4Chunk0Row_14_ok,
    tttLargeFiber70Block4Chunk0Row_15_ok]

def tttLargeFiber70Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber70Block4Chunk0ParentMapCheck 0
    && tttLargeFiber70Block4Chunk0ParentMapCheck 1
    && tttLargeFiber70Block4Chunk0ParentMapCheck 2
    && tttLargeFiber70Block4Chunk0ParentMapCheck 3
    && tttLargeFiber70Block4Chunk0ParentMapCheck 4
    && tttLargeFiber70Block4Chunk0ParentMapCheck 5
    && tttLargeFiber70Block4Chunk0ParentMapCheck 6
    && tttLargeFiber70Block4Chunk0ParentMapCheck 7
    && tttLargeFiber70Block4Chunk0ParentMapCheck 8
    && tttLargeFiber70Block4Chunk0ParentMapCheck 9
    && tttLargeFiber70Block4Chunk0ParentMapCheck 10
    && tttLargeFiber70Block4Chunk0ParentMapCheck 11
    && tttLargeFiber70Block4Chunk0ParentMapCheck 12
    && tttLargeFiber70Block4Chunk0ParentMapCheck 13
    && tttLargeFiber70Block4Chunk0ParentMapCheck 14
    && tttLargeFiber70Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber70Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber70Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber70Block4Chunk0ParentMapAudit,
    tttLargeFiber70Block4Chunk0ParentMap_0_ok,
    tttLargeFiber70Block4Chunk0ParentMap_1_ok,
    tttLargeFiber70Block4Chunk0ParentMap_2_ok,
    tttLargeFiber70Block4Chunk0ParentMap_3_ok,
    tttLargeFiber70Block4Chunk0ParentMap_4_ok,
    tttLargeFiber70Block4Chunk0ParentMap_5_ok,
    tttLargeFiber70Block4Chunk0ParentMap_6_ok,
    tttLargeFiber70Block4Chunk0ParentMap_7_ok,
    tttLargeFiber70Block4Chunk0ParentMap_8_ok,
    tttLargeFiber70Block4Chunk0ParentMap_9_ok,
    tttLargeFiber70Block4Chunk0ParentMap_10_ok,
    tttLargeFiber70Block4Chunk0ParentMap_11_ok,
    tttLargeFiber70Block4Chunk0ParentMap_12_ok,
    tttLargeFiber70Block4Chunk0ParentMap_13_ok,
    tttLargeFiber70Block4Chunk0ParentMap_14_ok,
    tttLargeFiber70Block4Chunk0ParentMap_15_ok]

def tttLargeFiber70Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber70Block4Chunk0ParentPathCheck 0
    && tttLargeFiber70Block4Chunk0ParentPathCheck 1
    && tttLargeFiber70Block4Chunk0ParentPathCheck 2
    && tttLargeFiber70Block4Chunk0ParentPathCheck 3
    && tttLargeFiber70Block4Chunk0ParentPathCheck 4
    && tttLargeFiber70Block4Chunk0ParentPathCheck 5
    && tttLargeFiber70Block4Chunk0ParentPathCheck 6
    && tttLargeFiber70Block4Chunk0ParentPathCheck 7
    && tttLargeFiber70Block4Chunk0ParentPathCheck 8
    && tttLargeFiber70Block4Chunk0ParentPathCheck 9
    && tttLargeFiber70Block4Chunk0ParentPathCheck 10
    && tttLargeFiber70Block4Chunk0ParentPathCheck 11
    && tttLargeFiber70Block4Chunk0ParentPathCheck 12
    && tttLargeFiber70Block4Chunk0ParentPathCheck 13
    && tttLargeFiber70Block4Chunk0ParentPathCheck 14
    && tttLargeFiber70Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber70Block4Chunk0ParentsAudit_ok :
    tttLargeFiber70Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber70Block4Chunk0ParentsAudit,
    tttLargeFiber70Block4Chunk0ParentPath_0_ok,
    tttLargeFiber70Block4Chunk0ParentPath_1_ok,
    tttLargeFiber70Block4Chunk0ParentPath_2_ok,
    tttLargeFiber70Block4Chunk0ParentPath_3_ok,
    tttLargeFiber70Block4Chunk0ParentPath_4_ok,
    tttLargeFiber70Block4Chunk0ParentPath_5_ok,
    tttLargeFiber70Block4Chunk0ParentPath_6_ok,
    tttLargeFiber70Block4Chunk0ParentPath_7_ok,
    tttLargeFiber70Block4Chunk0ParentPath_8_ok,
    tttLargeFiber70Block4Chunk0ParentPath_9_ok,
    tttLargeFiber70Block4Chunk0ParentPath_10_ok,
    tttLargeFiber70Block4Chunk0ParentPath_11_ok,
    tttLargeFiber70Block4Chunk0ParentPath_12_ok,
    tttLargeFiber70Block4Chunk0ParentPath_13_ok,
    tttLargeFiber70Block4Chunk0ParentPath_14_ok,
    tttLargeFiber70Block4Chunk0ParentPath_15_ok]

def tttLargeFiber70Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block4Chunk0SourcesCheck &&
    tttLargeFiber70Block4Chunk0RowsAudit &&
    tttLargeFiber70Block4Chunk0ParentMapAudit &&
    tttLargeFiber70Block4Chunk0ParentsAudit

theorem tttLargeFiber70Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber70Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block4Chunk0SourcesCheck_ok,
    tttLargeFiber70Block4Chunk0RowsAudit_ok,
    tttLargeFiber70Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber70Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
