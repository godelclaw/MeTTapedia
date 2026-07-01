import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 3 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block3Chunk2Sources : List Nat :=
  [   2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679,
   2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]

def tttLargeFiber10Row224 : TripleComponentParentRow :=
  tripleRow 2672 2640 75 40 148 75 24 80
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

def tttLargeFiber10Row225 : TripleComponentParentRow :=
  tripleRow 2673 2641 75 40 149 75 24 81
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

def tttLargeFiber10Row226 : TripleComponentParentRow :=
  tripleRow 2674 2642 75 40 150 75 24 82
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

def tttLargeFiber10Row227 : TripleComponentParentRow :=
  tripleRow 2675 2672 75 40 151 75 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row228 : TripleComponentParentRow :=
  tripleRow 2676 2672 75 40 164 75 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row229 : TripleComponentParentRow :=
  tripleRow 2677 2673 75 40 165 75 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row230 : TripleComponentParentRow :=
  tripleRow 2678 2646 75 40 166 75 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row231 : TripleComponentParentRow :=
  tripleRow 2679 2647 75 40 167 75 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row232 : TripleComponentParentRow :=
  tripleRow 2680 2648 75 41 156 75 25 88
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

def tttLargeFiber10Row233 : TripleComponentParentRow :=
  tripleRow 2681 2649 75 41 157 75 25 89
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

def tttLargeFiber10Row234 : TripleComponentParentRow :=
  tripleRow 2682 2650 75 41 158 75 25 90
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

def tttLargeFiber10Row235 : TripleComponentParentRow :=
  tripleRow 2683 2680 75 41 159 75 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row236 : TripleComponentParentRow :=
  tripleRow 2684 2680 75 41 172 75 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row237 : TripleComponentParentRow :=
  tripleRow 2685 2681 75 41 173 75 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row238 : TripleComponentParentRow :=
  tripleRow 2686 2654 75 41 174 75 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row239 : TripleComponentParentRow :=
  tripleRow 2687 2655 75 41 175 75 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row224
  , tttLargeFiber10Row225
  , tttLargeFiber10Row226
  , tttLargeFiber10Row227
  , tttLargeFiber10Row228
  , tttLargeFiber10Row229
  , tttLargeFiber10Row230
  , tttLargeFiber10Row231
  , tttLargeFiber10Row232
  , tttLargeFiber10Row233
  , tttLargeFiber10Row234
  , tttLargeFiber10Row235
  , tttLargeFiber10Row236
  , tttLargeFiber10Row237
  , tttLargeFiber10Row238
  , tttLargeFiber10Row239
  ]

def tttLargeFiber10Block3Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block3Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block3Chunk2ExpectedContains row.source &&
    tttLargeFiber10Block3Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber10Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber10Block3Chunk2Sources

theorem tttLargeFiber10Block3Chunk2SourcesCheck_ok :
    tttLargeFiber10Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber10Block3Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block3Chunk2RowValid
    (listGetD tttLargeFiber10Block3Chunk2Rows i default)

def tttLargeFiber10Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block3Chunk2Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block3Chunk2Sources 0 0 == 2672
      && tttLargeFiber10ParentOf 2672 == 2640
      && tttLargeFiber10ParentOf 2640 == 2512
      && tttLargeFiber10ParentOf 2512 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block3Chunk2Sources 1 0 == 2673
      && tttLargeFiber10ParentOf 2673 == 2641
      && tttLargeFiber10ParentOf 2641 == 2513
      && tttLargeFiber10ParentOf 2513 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block3Chunk2Sources 2 0 == 2674
      && tttLargeFiber10ParentOf 2674 == 2642
      && tttLargeFiber10ParentOf 2642 == 2514
      && tttLargeFiber10ParentOf 2514 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block3Chunk2Sources 3 0 == 2675
      && tttLargeFiber10ParentOf 2675 == 2672
      && tttLargeFiber10ParentOf 2672 == 2640
      && tttLargeFiber10ParentOf 2640 == 2512
      && tttLargeFiber10ParentOf 2512 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block3Chunk2Sources 4 0 == 2676
      && tttLargeFiber10ParentOf 2676 == 2672
      && tttLargeFiber10ParentOf 2672 == 2640
      && tttLargeFiber10ParentOf 2640 == 2512
      && tttLargeFiber10ParentOf 2512 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block3Chunk2Sources 5 0 == 2677
      && tttLargeFiber10ParentOf 2677 == 2673
      && tttLargeFiber10ParentOf 2673 == 2641
      && tttLargeFiber10ParentOf 2641 == 2513
      && tttLargeFiber10ParentOf 2513 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block3Chunk2Sources 6 0 == 2678
      && tttLargeFiber10ParentOf 2678 == 2646
      && tttLargeFiber10ParentOf 2646 == 2518
      && tttLargeFiber10ParentOf 2518 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block3Chunk2Sources 7 0 == 2679
      && tttLargeFiber10ParentOf 2679 == 2647
      && tttLargeFiber10ParentOf 2647 == 2519
      && tttLargeFiber10ParentOf 2519 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block3Chunk2Sources 8 0 == 2680
      && tttLargeFiber10ParentOf 2680 == 2648
      && tttLargeFiber10ParentOf 2648 == 2520
      && tttLargeFiber10ParentOf 2520 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block3Chunk2Sources 9 0 == 2681
      && tttLargeFiber10ParentOf 2681 == 2649
      && tttLargeFiber10ParentOf 2649 == 2521
      && tttLargeFiber10ParentOf 2521 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block3Chunk2Sources 10 0 == 2682
      && tttLargeFiber10ParentOf 2682 == 2650
      && tttLargeFiber10ParentOf 2650 == 2522
      && tttLargeFiber10ParentOf 2522 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block3Chunk2Sources 11 0 == 2683
      && tttLargeFiber10ParentOf 2683 == 2680
      && tttLargeFiber10ParentOf 2680 == 2648
      && tttLargeFiber10ParentOf 2648 == 2520
      && tttLargeFiber10ParentOf 2520 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block3Chunk2Sources 12 0 == 2684
      && tttLargeFiber10ParentOf 2684 == 2680
      && tttLargeFiber10ParentOf 2680 == 2648
      && tttLargeFiber10ParentOf 2648 == 2520
      && tttLargeFiber10ParentOf 2520 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block3Chunk2Sources 13 0 == 2685
      && tttLargeFiber10ParentOf 2685 == 2681
      && tttLargeFiber10ParentOf 2681 == 2649
      && tttLargeFiber10ParentOf 2649 == 2521
      && tttLargeFiber10ParentOf 2521 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block3Chunk2Sources 14 0 == 2686
      && tttLargeFiber10ParentOf 2686 == 2654
      && tttLargeFiber10ParentOf 2654 == 2526
      && tttLargeFiber10ParentOf 2526 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block3Chunk2Sources 15 0 == 2687
      && tttLargeFiber10ParentOf 2687 == 2655
      && tttLargeFiber10ParentOf 2655 == 2527
      && tttLargeFiber10ParentOf 2527 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block3Chunk2Row_0_ok :
    tttLargeFiber10Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_1_ok :
    tttLargeFiber10Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_2_ok :
    tttLargeFiber10Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_3_ok :
    tttLargeFiber10Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_4_ok :
    tttLargeFiber10Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_5_ok :
    tttLargeFiber10Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_6_ok :
    tttLargeFiber10Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_7_ok :
    tttLargeFiber10Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_8_ok :
    tttLargeFiber10Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_9_ok :
    tttLargeFiber10Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_10_ok :
    tttLargeFiber10Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_11_ok :
    tttLargeFiber10Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_12_ok :
    tttLargeFiber10Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_13_ok :
    tttLargeFiber10Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_14_ok :
    tttLargeFiber10Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2Row_15_ok :
    tttLargeFiber10Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_0_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_1_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_2_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_3_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_4_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_5_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_6_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_7_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_8_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_9_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_10_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_11_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_12_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_13_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_14_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentMap_15_ok :
    tttLargeFiber10Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_0_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_1_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_2_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_3_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_4_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_5_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_6_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_7_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_8_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_9_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_10_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_11_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_12_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_13_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_14_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block3Chunk2ParentPath_15_ok :
    tttLargeFiber10Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber10Block3Chunk2RowCheck 0
    && tttLargeFiber10Block3Chunk2RowCheck 1
    && tttLargeFiber10Block3Chunk2RowCheck 2
    && tttLargeFiber10Block3Chunk2RowCheck 3
    && tttLargeFiber10Block3Chunk2RowCheck 4
    && tttLargeFiber10Block3Chunk2RowCheck 5
    && tttLargeFiber10Block3Chunk2RowCheck 6
    && tttLargeFiber10Block3Chunk2RowCheck 7
    && tttLargeFiber10Block3Chunk2RowCheck 8
    && tttLargeFiber10Block3Chunk2RowCheck 9
    && tttLargeFiber10Block3Chunk2RowCheck 10
    && tttLargeFiber10Block3Chunk2RowCheck 11
    && tttLargeFiber10Block3Chunk2RowCheck 12
    && tttLargeFiber10Block3Chunk2RowCheck 13
    && tttLargeFiber10Block3Chunk2RowCheck 14
    && tttLargeFiber10Block3Chunk2RowCheck 15

theorem tttLargeFiber10Block3Chunk2RowsAudit_ok :
    tttLargeFiber10Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber10Block3Chunk2RowsAudit,
    tttLargeFiber10Block3Chunk2Row_0_ok,
    tttLargeFiber10Block3Chunk2Row_1_ok,
    tttLargeFiber10Block3Chunk2Row_2_ok,
    tttLargeFiber10Block3Chunk2Row_3_ok,
    tttLargeFiber10Block3Chunk2Row_4_ok,
    tttLargeFiber10Block3Chunk2Row_5_ok,
    tttLargeFiber10Block3Chunk2Row_6_ok,
    tttLargeFiber10Block3Chunk2Row_7_ok,
    tttLargeFiber10Block3Chunk2Row_8_ok,
    tttLargeFiber10Block3Chunk2Row_9_ok,
    tttLargeFiber10Block3Chunk2Row_10_ok,
    tttLargeFiber10Block3Chunk2Row_11_ok,
    tttLargeFiber10Block3Chunk2Row_12_ok,
    tttLargeFiber10Block3Chunk2Row_13_ok,
    tttLargeFiber10Block3Chunk2Row_14_ok,
    tttLargeFiber10Block3Chunk2Row_15_ok]

def tttLargeFiber10Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber10Block3Chunk2ParentMapCheck 0
    && tttLargeFiber10Block3Chunk2ParentMapCheck 1
    && tttLargeFiber10Block3Chunk2ParentMapCheck 2
    && tttLargeFiber10Block3Chunk2ParentMapCheck 3
    && tttLargeFiber10Block3Chunk2ParentMapCheck 4
    && tttLargeFiber10Block3Chunk2ParentMapCheck 5
    && tttLargeFiber10Block3Chunk2ParentMapCheck 6
    && tttLargeFiber10Block3Chunk2ParentMapCheck 7
    && tttLargeFiber10Block3Chunk2ParentMapCheck 8
    && tttLargeFiber10Block3Chunk2ParentMapCheck 9
    && tttLargeFiber10Block3Chunk2ParentMapCheck 10
    && tttLargeFiber10Block3Chunk2ParentMapCheck 11
    && tttLargeFiber10Block3Chunk2ParentMapCheck 12
    && tttLargeFiber10Block3Chunk2ParentMapCheck 13
    && tttLargeFiber10Block3Chunk2ParentMapCheck 14
    && tttLargeFiber10Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber10Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber10Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber10Block3Chunk2ParentMapAudit,
    tttLargeFiber10Block3Chunk2ParentMap_0_ok,
    tttLargeFiber10Block3Chunk2ParentMap_1_ok,
    tttLargeFiber10Block3Chunk2ParentMap_2_ok,
    tttLargeFiber10Block3Chunk2ParentMap_3_ok,
    tttLargeFiber10Block3Chunk2ParentMap_4_ok,
    tttLargeFiber10Block3Chunk2ParentMap_5_ok,
    tttLargeFiber10Block3Chunk2ParentMap_6_ok,
    tttLargeFiber10Block3Chunk2ParentMap_7_ok,
    tttLargeFiber10Block3Chunk2ParentMap_8_ok,
    tttLargeFiber10Block3Chunk2ParentMap_9_ok,
    tttLargeFiber10Block3Chunk2ParentMap_10_ok,
    tttLargeFiber10Block3Chunk2ParentMap_11_ok,
    tttLargeFiber10Block3Chunk2ParentMap_12_ok,
    tttLargeFiber10Block3Chunk2ParentMap_13_ok,
    tttLargeFiber10Block3Chunk2ParentMap_14_ok,
    tttLargeFiber10Block3Chunk2ParentMap_15_ok]

def tttLargeFiber10Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber10Block3Chunk2ParentPathCheck 0
    && tttLargeFiber10Block3Chunk2ParentPathCheck 1
    && tttLargeFiber10Block3Chunk2ParentPathCheck 2
    && tttLargeFiber10Block3Chunk2ParentPathCheck 3
    && tttLargeFiber10Block3Chunk2ParentPathCheck 4
    && tttLargeFiber10Block3Chunk2ParentPathCheck 5
    && tttLargeFiber10Block3Chunk2ParentPathCheck 6
    && tttLargeFiber10Block3Chunk2ParentPathCheck 7
    && tttLargeFiber10Block3Chunk2ParentPathCheck 8
    && tttLargeFiber10Block3Chunk2ParentPathCheck 9
    && tttLargeFiber10Block3Chunk2ParentPathCheck 10
    && tttLargeFiber10Block3Chunk2ParentPathCheck 11
    && tttLargeFiber10Block3Chunk2ParentPathCheck 12
    && tttLargeFiber10Block3Chunk2ParentPathCheck 13
    && tttLargeFiber10Block3Chunk2ParentPathCheck 14
    && tttLargeFiber10Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber10Block3Chunk2ParentsAudit_ok :
    tttLargeFiber10Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber10Block3Chunk2ParentsAudit,
    tttLargeFiber10Block3Chunk2ParentPath_0_ok,
    tttLargeFiber10Block3Chunk2ParentPath_1_ok,
    tttLargeFiber10Block3Chunk2ParentPath_2_ok,
    tttLargeFiber10Block3Chunk2ParentPath_3_ok,
    tttLargeFiber10Block3Chunk2ParentPath_4_ok,
    tttLargeFiber10Block3Chunk2ParentPath_5_ok,
    tttLargeFiber10Block3Chunk2ParentPath_6_ok,
    tttLargeFiber10Block3Chunk2ParentPath_7_ok,
    tttLargeFiber10Block3Chunk2ParentPath_8_ok,
    tttLargeFiber10Block3Chunk2ParentPath_9_ok,
    tttLargeFiber10Block3Chunk2ParentPath_10_ok,
    tttLargeFiber10Block3Chunk2ParentPath_11_ok,
    tttLargeFiber10Block3Chunk2ParentPath_12_ok,
    tttLargeFiber10Block3Chunk2ParentPath_13_ok,
    tttLargeFiber10Block3Chunk2ParentPath_14_ok,
    tttLargeFiber10Block3Chunk2ParentPath_15_ok]

def tttLargeFiber10Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block3Chunk2SourcesCheck &&
    tttLargeFiber10Block3Chunk2RowsAudit &&
    tttLargeFiber10Block3Chunk2ParentMapAudit &&
    tttLargeFiber10Block3Chunk2ParentsAudit

theorem tttLargeFiber10Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber10Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block3Chunk2SourcesCheck_ok,
    tttLargeFiber10Block3Chunk2RowsAudit_ok,
    tttLargeFiber10Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber10Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
