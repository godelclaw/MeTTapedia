import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 3 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block3Chunk3Sources : List Nat :=
  [   2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695,
   2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]

def tttLargeFiber10Row240 : TripleComponentParentRow :=
  tripleRow 2688 2560 75 42 0 73 110 64
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

def tttLargeFiber10Row241 : TripleComponentParentRow :=
  tripleRow 2689 2561 75 42 1 73 110 65
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

def tttLargeFiber10Row242 : TripleComponentParentRow :=
  tripleRow 2690 2562 75 42 2 73 110 66
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

def tttLargeFiber10Row243 : TripleComponentParentRow :=
  tripleRow 2691 2563 75 42 3 73 110 67
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

def tttLargeFiber10Row244 : TripleComponentParentRow :=
  tripleRow 2692 2688 75 42 48 75 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row245 : TripleComponentParentRow :=
  tripleRow 2693 2689 75 42 49 75 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row246 : TripleComponentParentRow :=
  tripleRow 2694 2566 75 42 50 73 110 118
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

def tttLargeFiber10Row247 : TripleComponentParentRow :=
  tripleRow 2695 2567 75 42 51 73 110 119
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

def tttLargeFiber10Row248 : TripleComponentParentRow :=
  tripleRow 2696 2568 75 43 8 73 111 72
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

def tttLargeFiber10Row249 : TripleComponentParentRow :=
  tripleRow 2697 2569 75 43 9 73 111 73
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

def tttLargeFiber10Row250 : TripleComponentParentRow :=
  tripleRow 2698 2570 75 43 10 73 111 74
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

def tttLargeFiber10Row251 : TripleComponentParentRow :=
  tripleRow 2699 2571 75 43 11 73 111 75
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

def tttLargeFiber10Row252 : TripleComponentParentRow :=
  tripleRow 2700 2696 75 43 56 75 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row253 : TripleComponentParentRow :=
  tripleRow 2701 2697 75 43 57 75 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row254 : TripleComponentParentRow :=
  tripleRow 2702 2574 75 43 58 73 111 126
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

def tttLargeFiber10Row255 : TripleComponentParentRow :=
  tripleRow 2703 2575 75 43 59 73 111 127
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

def tttLargeFiber10Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row240
  , tttLargeFiber10Row241
  , tttLargeFiber10Row242
  , tttLargeFiber10Row243
  , tttLargeFiber10Row244
  , tttLargeFiber10Row245
  , tttLargeFiber10Row246
  , tttLargeFiber10Row247
  , tttLargeFiber10Row248
  , tttLargeFiber10Row249
  , tttLargeFiber10Row250
  , tttLargeFiber10Row251
  , tttLargeFiber10Row252
  , tttLargeFiber10Row253
  , tttLargeFiber10Row254
  , tttLargeFiber10Row255
  ]

def tttLargeFiber10Block3Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block3Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block3Chunk3ExpectedContains row.source &&
    tttLargeFiber10Block3Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber10Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber10Block3Chunk3Sources

theorem tttLargeFiber10Block3Chunk3SourcesCheck_ok :
    tttLargeFiber10Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber10Block3Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block3Chunk3RowValid
    (listGetD tttLargeFiber10Block3Chunk3Rows i default)

def tttLargeFiber10Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block3Chunk3Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block3Chunk3Sources 0 0 == 2688
      && tttLargeFiber10ParentOf 2688 == 2560
      && tttLargeFiber10ParentOf 2560 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block3Chunk3Sources 1 0 == 2689
      && tttLargeFiber10ParentOf 2689 == 2561
      && tttLargeFiber10ParentOf 2561 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block3Chunk3Sources 2 0 == 2690
      && tttLargeFiber10ParentOf 2690 == 2562
      && tttLargeFiber10ParentOf 2562 == 2498
      && tttLargeFiber10ParentOf 2498 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block3Chunk3Sources 3 0 == 2691
      && tttLargeFiber10ParentOf 2691 == 2563
      && tttLargeFiber10ParentOf 2563 == 2499
      && tttLargeFiber10ParentOf 2499 == 2459
      && tttLargeFiber10ParentOf 2459 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block3Chunk3Sources 4 0 == 2692
      && tttLargeFiber10ParentOf 2692 == 2688
      && tttLargeFiber10ParentOf 2688 == 2560
      && tttLargeFiber10ParentOf 2560 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block3Chunk3Sources 5 0 == 2693
      && tttLargeFiber10ParentOf 2693 == 2689
      && tttLargeFiber10ParentOf 2689 == 2561
      && tttLargeFiber10ParentOf 2561 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block3Chunk3Sources 6 0 == 2694
      && tttLargeFiber10ParentOf 2694 == 2566
      && tttLargeFiber10ParentOf 2566 == 2502
      && tttLargeFiber10ParentOf 2502 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block3Chunk3Sources 7 0 == 2695
      && tttLargeFiber10ParentOf 2695 == 2567
      && tttLargeFiber10ParentOf 2567 == 2503
      && tttLargeFiber10ParentOf 2503 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block3Chunk3Sources 8 0 == 2696
      && tttLargeFiber10ParentOf 2696 == 2568
      && tttLargeFiber10ParentOf 2568 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block3Chunk3Sources 9 0 == 2697
      && tttLargeFiber10ParentOf 2697 == 2569
      && tttLargeFiber10ParentOf 2569 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block3Chunk3Sources 10 0 == 2698
      && tttLargeFiber10ParentOf 2698 == 2570
      && tttLargeFiber10ParentOf 2570 == 2506
      && tttLargeFiber10ParentOf 2506 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block3Chunk3Sources 11 0 == 2699
      && tttLargeFiber10ParentOf 2699 == 2571
      && tttLargeFiber10ParentOf 2571 == 2507
      && tttLargeFiber10ParentOf 2507 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block3Chunk3Sources 12 0 == 2700
      && tttLargeFiber10ParentOf 2700 == 2696
      && tttLargeFiber10ParentOf 2696 == 2568
      && tttLargeFiber10ParentOf 2568 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block3Chunk3Sources 13 0 == 2701
      && tttLargeFiber10ParentOf 2701 == 2697
      && tttLargeFiber10ParentOf 2697 == 2569
      && tttLargeFiber10ParentOf 2569 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block3Chunk3Sources 14 0 == 2702
      && tttLargeFiber10ParentOf 2702 == 2574
      && tttLargeFiber10ParentOf 2574 == 2510
      && tttLargeFiber10ParentOf 2510 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block3Chunk3Sources 15 0 == 2703
      && tttLargeFiber10ParentOf 2703 == 2575
      && tttLargeFiber10ParentOf 2575 == 2511
      && tttLargeFiber10ParentOf 2511 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block3Chunk3Row_0_ok :
    tttLargeFiber10Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_1_ok :
    tttLargeFiber10Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_2_ok :
    tttLargeFiber10Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_3_ok :
    tttLargeFiber10Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_4_ok :
    tttLargeFiber10Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_5_ok :
    tttLargeFiber10Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_6_ok :
    tttLargeFiber10Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_7_ok :
    tttLargeFiber10Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_8_ok :
    tttLargeFiber10Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_9_ok :
    tttLargeFiber10Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_10_ok :
    tttLargeFiber10Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_11_ok :
    tttLargeFiber10Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_12_ok :
    tttLargeFiber10Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_13_ok :
    tttLargeFiber10Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_14_ok :
    tttLargeFiber10Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3Row_15_ok :
    tttLargeFiber10Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_0_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_1_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_2_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_3_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_4_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_5_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_6_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_7_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_8_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_9_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_10_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_11_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_12_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_13_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_14_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentMap_15_ok :
    tttLargeFiber10Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_0_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_1_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_2_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_3_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_4_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_5_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_6_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_7_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_8_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_9_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_10_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_11_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_12_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_13_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_14_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block3Chunk3ParentPath_15_ok :
    tttLargeFiber10Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber10Block3Chunk3RowCheck 0
    && tttLargeFiber10Block3Chunk3RowCheck 1
    && tttLargeFiber10Block3Chunk3RowCheck 2
    && tttLargeFiber10Block3Chunk3RowCheck 3
    && tttLargeFiber10Block3Chunk3RowCheck 4
    && tttLargeFiber10Block3Chunk3RowCheck 5
    && tttLargeFiber10Block3Chunk3RowCheck 6
    && tttLargeFiber10Block3Chunk3RowCheck 7
    && tttLargeFiber10Block3Chunk3RowCheck 8
    && tttLargeFiber10Block3Chunk3RowCheck 9
    && tttLargeFiber10Block3Chunk3RowCheck 10
    && tttLargeFiber10Block3Chunk3RowCheck 11
    && tttLargeFiber10Block3Chunk3RowCheck 12
    && tttLargeFiber10Block3Chunk3RowCheck 13
    && tttLargeFiber10Block3Chunk3RowCheck 14
    && tttLargeFiber10Block3Chunk3RowCheck 15

theorem tttLargeFiber10Block3Chunk3RowsAudit_ok :
    tttLargeFiber10Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber10Block3Chunk3RowsAudit,
    tttLargeFiber10Block3Chunk3Row_0_ok,
    tttLargeFiber10Block3Chunk3Row_1_ok,
    tttLargeFiber10Block3Chunk3Row_2_ok,
    tttLargeFiber10Block3Chunk3Row_3_ok,
    tttLargeFiber10Block3Chunk3Row_4_ok,
    tttLargeFiber10Block3Chunk3Row_5_ok,
    tttLargeFiber10Block3Chunk3Row_6_ok,
    tttLargeFiber10Block3Chunk3Row_7_ok,
    tttLargeFiber10Block3Chunk3Row_8_ok,
    tttLargeFiber10Block3Chunk3Row_9_ok,
    tttLargeFiber10Block3Chunk3Row_10_ok,
    tttLargeFiber10Block3Chunk3Row_11_ok,
    tttLargeFiber10Block3Chunk3Row_12_ok,
    tttLargeFiber10Block3Chunk3Row_13_ok,
    tttLargeFiber10Block3Chunk3Row_14_ok,
    tttLargeFiber10Block3Chunk3Row_15_ok]

def tttLargeFiber10Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber10Block3Chunk3ParentMapCheck 0
    && tttLargeFiber10Block3Chunk3ParentMapCheck 1
    && tttLargeFiber10Block3Chunk3ParentMapCheck 2
    && tttLargeFiber10Block3Chunk3ParentMapCheck 3
    && tttLargeFiber10Block3Chunk3ParentMapCheck 4
    && tttLargeFiber10Block3Chunk3ParentMapCheck 5
    && tttLargeFiber10Block3Chunk3ParentMapCheck 6
    && tttLargeFiber10Block3Chunk3ParentMapCheck 7
    && tttLargeFiber10Block3Chunk3ParentMapCheck 8
    && tttLargeFiber10Block3Chunk3ParentMapCheck 9
    && tttLargeFiber10Block3Chunk3ParentMapCheck 10
    && tttLargeFiber10Block3Chunk3ParentMapCheck 11
    && tttLargeFiber10Block3Chunk3ParentMapCheck 12
    && tttLargeFiber10Block3Chunk3ParentMapCheck 13
    && tttLargeFiber10Block3Chunk3ParentMapCheck 14
    && tttLargeFiber10Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber10Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber10Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber10Block3Chunk3ParentMapAudit,
    tttLargeFiber10Block3Chunk3ParentMap_0_ok,
    tttLargeFiber10Block3Chunk3ParentMap_1_ok,
    tttLargeFiber10Block3Chunk3ParentMap_2_ok,
    tttLargeFiber10Block3Chunk3ParentMap_3_ok,
    tttLargeFiber10Block3Chunk3ParentMap_4_ok,
    tttLargeFiber10Block3Chunk3ParentMap_5_ok,
    tttLargeFiber10Block3Chunk3ParentMap_6_ok,
    tttLargeFiber10Block3Chunk3ParentMap_7_ok,
    tttLargeFiber10Block3Chunk3ParentMap_8_ok,
    tttLargeFiber10Block3Chunk3ParentMap_9_ok,
    tttLargeFiber10Block3Chunk3ParentMap_10_ok,
    tttLargeFiber10Block3Chunk3ParentMap_11_ok,
    tttLargeFiber10Block3Chunk3ParentMap_12_ok,
    tttLargeFiber10Block3Chunk3ParentMap_13_ok,
    tttLargeFiber10Block3Chunk3ParentMap_14_ok,
    tttLargeFiber10Block3Chunk3ParentMap_15_ok]

def tttLargeFiber10Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber10Block3Chunk3ParentPathCheck 0
    && tttLargeFiber10Block3Chunk3ParentPathCheck 1
    && tttLargeFiber10Block3Chunk3ParentPathCheck 2
    && tttLargeFiber10Block3Chunk3ParentPathCheck 3
    && tttLargeFiber10Block3Chunk3ParentPathCheck 4
    && tttLargeFiber10Block3Chunk3ParentPathCheck 5
    && tttLargeFiber10Block3Chunk3ParentPathCheck 6
    && tttLargeFiber10Block3Chunk3ParentPathCheck 7
    && tttLargeFiber10Block3Chunk3ParentPathCheck 8
    && tttLargeFiber10Block3Chunk3ParentPathCheck 9
    && tttLargeFiber10Block3Chunk3ParentPathCheck 10
    && tttLargeFiber10Block3Chunk3ParentPathCheck 11
    && tttLargeFiber10Block3Chunk3ParentPathCheck 12
    && tttLargeFiber10Block3Chunk3ParentPathCheck 13
    && tttLargeFiber10Block3Chunk3ParentPathCheck 14
    && tttLargeFiber10Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber10Block3Chunk3ParentsAudit_ok :
    tttLargeFiber10Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber10Block3Chunk3ParentsAudit,
    tttLargeFiber10Block3Chunk3ParentPath_0_ok,
    tttLargeFiber10Block3Chunk3ParentPath_1_ok,
    tttLargeFiber10Block3Chunk3ParentPath_2_ok,
    tttLargeFiber10Block3Chunk3ParentPath_3_ok,
    tttLargeFiber10Block3Chunk3ParentPath_4_ok,
    tttLargeFiber10Block3Chunk3ParentPath_5_ok,
    tttLargeFiber10Block3Chunk3ParentPath_6_ok,
    tttLargeFiber10Block3Chunk3ParentPath_7_ok,
    tttLargeFiber10Block3Chunk3ParentPath_8_ok,
    tttLargeFiber10Block3Chunk3ParentPath_9_ok,
    tttLargeFiber10Block3Chunk3ParentPath_10_ok,
    tttLargeFiber10Block3Chunk3ParentPath_11_ok,
    tttLargeFiber10Block3Chunk3ParentPath_12_ok,
    tttLargeFiber10Block3Chunk3ParentPath_13_ok,
    tttLargeFiber10Block3Chunk3ParentPath_14_ok,
    tttLargeFiber10Block3Chunk3ParentPath_15_ok]

def tttLargeFiber10Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block3Chunk3SourcesCheck &&
    tttLargeFiber10Block3Chunk3RowsAudit &&
    tttLargeFiber10Block3Chunk3ParentMapAudit &&
    tttLargeFiber10Block3Chunk3ParentsAudit

theorem tttLargeFiber10Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber10Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block3Chunk3SourcesCheck_ok,
    tttLargeFiber10Block3Chunk3RowsAudit_ok,
    tttLargeFiber10Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber10Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
