import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block1Chunk3Sources : List Nat :=
  [   2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567,
   2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]

def tttLargeFiber10Row112 : TripleComponentParentRow :=
  tripleRow 2560 2496 73 110 64 72 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row113 : TripleComponentParentRow :=
  tripleRow 2561 2497 73 110 65 72 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row114 : TripleComponentParentRow :=
  tripleRow 2562 2498 73 110 66 72 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row115 : TripleComponentParentRow :=
  tripleRow 2563 2499 73 110 67 72 102 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row116 : TripleComponentParentRow :=
  tripleRow 2564 2500 73 110 116 72 102 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row117 : TripleComponentParentRow :=
  tripleRow 2565 2501 73 110 117 72 102 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row118 : TripleComponentParentRow :=
  tripleRow 2566 2502 73 110 118 72 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row119 : TripleComponentParentRow :=
  tripleRow 2567 2503 73 110 119 72 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row120 : TripleComponentParentRow :=
  tripleRow 2568 2504 73 111 72 72 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row121 : TripleComponentParentRow :=
  tripleRow 2569 2505 73 111 73 72 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row122 : TripleComponentParentRow :=
  tripleRow 2570 2506 73 111 74 72 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row123 : TripleComponentParentRow :=
  tripleRow 2571 2507 73 111 75 72 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row124 : TripleComponentParentRow :=
  tripleRow 2572 2508 73 111 124 72 103 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row125 : TripleComponentParentRow :=
  tripleRow 2573 2509 73 111 125 72 103 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row126 : TripleComponentParentRow :=
  tripleRow 2574 2510 73 111 126 72 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row127 : TripleComponentParentRow :=
  tripleRow 2575 2511 73 111 127 72 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row112
  , tttLargeFiber10Row113
  , tttLargeFiber10Row114
  , tttLargeFiber10Row115
  , tttLargeFiber10Row116
  , tttLargeFiber10Row117
  , tttLargeFiber10Row118
  , tttLargeFiber10Row119
  , tttLargeFiber10Row120
  , tttLargeFiber10Row121
  , tttLargeFiber10Row122
  , tttLargeFiber10Row123
  , tttLargeFiber10Row124
  , tttLargeFiber10Row125
  , tttLargeFiber10Row126
  , tttLargeFiber10Row127
  ]

def tttLargeFiber10Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber10Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber10Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber10Block1Chunk3Sources

theorem tttLargeFiber10Block1Chunk3SourcesCheck_ok :
    tttLargeFiber10Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber10Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block1Chunk3RowValid
    (listGetD tttLargeFiber10Block1Chunk3Rows i default)

def tttLargeFiber10Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block1Chunk3Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block1Chunk3Sources 0 0 == 2560
      && tttLargeFiber10ParentOf 2560 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block1Chunk3Sources 1 0 == 2561
      && tttLargeFiber10ParentOf 2561 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block1Chunk3Sources 2 0 == 2562
      && tttLargeFiber10ParentOf 2562 == 2498
      && tttLargeFiber10ParentOf 2498 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block1Chunk3Sources 3 0 == 2563
      && tttLargeFiber10ParentOf 2563 == 2499
      && tttLargeFiber10ParentOf 2499 == 2459
      && tttLargeFiber10ParentOf 2459 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block1Chunk3Sources 4 0 == 2564
      && tttLargeFiber10ParentOf 2564 == 2500
      && tttLargeFiber10ParentOf 2500 == 2460
      && tttLargeFiber10ParentOf 2460 == 2452
      && tttLargeFiber10ParentOf 2452 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block1Chunk3Sources 5 0 == 2565
      && tttLargeFiber10ParentOf 2565 == 2501
      && tttLargeFiber10ParentOf 2501 == 2461
      && tttLargeFiber10ParentOf 2461 == 2453
      && tttLargeFiber10ParentOf 2453 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block1Chunk3Sources 6 0 == 2566
      && tttLargeFiber10ParentOf 2566 == 2502
      && tttLargeFiber10ParentOf 2502 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block1Chunk3Sources 7 0 == 2567
      && tttLargeFiber10ParentOf 2567 == 2503
      && tttLargeFiber10ParentOf 2503 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block1Chunk3Sources 8 0 == 2568
      && tttLargeFiber10ParentOf 2568 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block1Chunk3Sources 9 0 == 2569
      && tttLargeFiber10ParentOf 2569 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block1Chunk3Sources 10 0 == 2570
      && tttLargeFiber10ParentOf 2570 == 2506
      && tttLargeFiber10ParentOf 2506 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block1Chunk3Sources 11 0 == 2571
      && tttLargeFiber10ParentOf 2571 == 2507
      && tttLargeFiber10ParentOf 2507 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block1Chunk3Sources 12 0 == 2572
      && tttLargeFiber10ParentOf 2572 == 2508
      && tttLargeFiber10ParentOf 2508 == 2452
      && tttLargeFiber10ParentOf 2452 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block1Chunk3Sources 13 0 == 2573
      && tttLargeFiber10ParentOf 2573 == 2509
      && tttLargeFiber10ParentOf 2509 == 2453
      && tttLargeFiber10ParentOf 2453 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block1Chunk3Sources 14 0 == 2574
      && tttLargeFiber10ParentOf 2574 == 2510
      && tttLargeFiber10ParentOf 2510 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block1Chunk3Sources 15 0 == 2575
      && tttLargeFiber10ParentOf 2575 == 2511
      && tttLargeFiber10ParentOf 2511 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block1Chunk3Row_0_ok :
    tttLargeFiber10Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_1_ok :
    tttLargeFiber10Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_2_ok :
    tttLargeFiber10Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_3_ok :
    tttLargeFiber10Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_4_ok :
    tttLargeFiber10Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_5_ok :
    tttLargeFiber10Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_6_ok :
    tttLargeFiber10Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_7_ok :
    tttLargeFiber10Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_8_ok :
    tttLargeFiber10Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_9_ok :
    tttLargeFiber10Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_10_ok :
    tttLargeFiber10Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_11_ok :
    tttLargeFiber10Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_12_ok :
    tttLargeFiber10Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_13_ok :
    tttLargeFiber10Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_14_ok :
    tttLargeFiber10Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3Row_15_ok :
    tttLargeFiber10Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_0_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_1_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_2_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_3_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_4_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_5_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_6_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_7_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_8_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_9_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_10_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_11_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_12_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_13_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_14_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentMap_15_ok :
    tttLargeFiber10Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_0_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_1_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_2_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_3_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_4_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_5_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_6_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_7_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_8_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_9_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_10_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_11_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_12_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_13_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_14_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk3ParentPath_15_ok :
    tttLargeFiber10Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber10Block1Chunk3RowCheck 0
    && tttLargeFiber10Block1Chunk3RowCheck 1
    && tttLargeFiber10Block1Chunk3RowCheck 2
    && tttLargeFiber10Block1Chunk3RowCheck 3
    && tttLargeFiber10Block1Chunk3RowCheck 4
    && tttLargeFiber10Block1Chunk3RowCheck 5
    && tttLargeFiber10Block1Chunk3RowCheck 6
    && tttLargeFiber10Block1Chunk3RowCheck 7
    && tttLargeFiber10Block1Chunk3RowCheck 8
    && tttLargeFiber10Block1Chunk3RowCheck 9
    && tttLargeFiber10Block1Chunk3RowCheck 10
    && tttLargeFiber10Block1Chunk3RowCheck 11
    && tttLargeFiber10Block1Chunk3RowCheck 12
    && tttLargeFiber10Block1Chunk3RowCheck 13
    && tttLargeFiber10Block1Chunk3RowCheck 14
    && tttLargeFiber10Block1Chunk3RowCheck 15

theorem tttLargeFiber10Block1Chunk3RowsAudit_ok :
    tttLargeFiber10Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber10Block1Chunk3RowsAudit,
    tttLargeFiber10Block1Chunk3Row_0_ok,
    tttLargeFiber10Block1Chunk3Row_1_ok,
    tttLargeFiber10Block1Chunk3Row_2_ok,
    tttLargeFiber10Block1Chunk3Row_3_ok,
    tttLargeFiber10Block1Chunk3Row_4_ok,
    tttLargeFiber10Block1Chunk3Row_5_ok,
    tttLargeFiber10Block1Chunk3Row_6_ok,
    tttLargeFiber10Block1Chunk3Row_7_ok,
    tttLargeFiber10Block1Chunk3Row_8_ok,
    tttLargeFiber10Block1Chunk3Row_9_ok,
    tttLargeFiber10Block1Chunk3Row_10_ok,
    tttLargeFiber10Block1Chunk3Row_11_ok,
    tttLargeFiber10Block1Chunk3Row_12_ok,
    tttLargeFiber10Block1Chunk3Row_13_ok,
    tttLargeFiber10Block1Chunk3Row_14_ok,
    tttLargeFiber10Block1Chunk3Row_15_ok]

def tttLargeFiber10Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber10Block1Chunk3ParentMapCheck 0
    && tttLargeFiber10Block1Chunk3ParentMapCheck 1
    && tttLargeFiber10Block1Chunk3ParentMapCheck 2
    && tttLargeFiber10Block1Chunk3ParentMapCheck 3
    && tttLargeFiber10Block1Chunk3ParentMapCheck 4
    && tttLargeFiber10Block1Chunk3ParentMapCheck 5
    && tttLargeFiber10Block1Chunk3ParentMapCheck 6
    && tttLargeFiber10Block1Chunk3ParentMapCheck 7
    && tttLargeFiber10Block1Chunk3ParentMapCheck 8
    && tttLargeFiber10Block1Chunk3ParentMapCheck 9
    && tttLargeFiber10Block1Chunk3ParentMapCheck 10
    && tttLargeFiber10Block1Chunk3ParentMapCheck 11
    && tttLargeFiber10Block1Chunk3ParentMapCheck 12
    && tttLargeFiber10Block1Chunk3ParentMapCheck 13
    && tttLargeFiber10Block1Chunk3ParentMapCheck 14
    && tttLargeFiber10Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber10Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber10Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber10Block1Chunk3ParentMapAudit,
    tttLargeFiber10Block1Chunk3ParentMap_0_ok,
    tttLargeFiber10Block1Chunk3ParentMap_1_ok,
    tttLargeFiber10Block1Chunk3ParentMap_2_ok,
    tttLargeFiber10Block1Chunk3ParentMap_3_ok,
    tttLargeFiber10Block1Chunk3ParentMap_4_ok,
    tttLargeFiber10Block1Chunk3ParentMap_5_ok,
    tttLargeFiber10Block1Chunk3ParentMap_6_ok,
    tttLargeFiber10Block1Chunk3ParentMap_7_ok,
    tttLargeFiber10Block1Chunk3ParentMap_8_ok,
    tttLargeFiber10Block1Chunk3ParentMap_9_ok,
    tttLargeFiber10Block1Chunk3ParentMap_10_ok,
    tttLargeFiber10Block1Chunk3ParentMap_11_ok,
    tttLargeFiber10Block1Chunk3ParentMap_12_ok,
    tttLargeFiber10Block1Chunk3ParentMap_13_ok,
    tttLargeFiber10Block1Chunk3ParentMap_14_ok,
    tttLargeFiber10Block1Chunk3ParentMap_15_ok]

def tttLargeFiber10Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber10Block1Chunk3ParentPathCheck 0
    && tttLargeFiber10Block1Chunk3ParentPathCheck 1
    && tttLargeFiber10Block1Chunk3ParentPathCheck 2
    && tttLargeFiber10Block1Chunk3ParentPathCheck 3
    && tttLargeFiber10Block1Chunk3ParentPathCheck 4
    && tttLargeFiber10Block1Chunk3ParentPathCheck 5
    && tttLargeFiber10Block1Chunk3ParentPathCheck 6
    && tttLargeFiber10Block1Chunk3ParentPathCheck 7
    && tttLargeFiber10Block1Chunk3ParentPathCheck 8
    && tttLargeFiber10Block1Chunk3ParentPathCheck 9
    && tttLargeFiber10Block1Chunk3ParentPathCheck 10
    && tttLargeFiber10Block1Chunk3ParentPathCheck 11
    && tttLargeFiber10Block1Chunk3ParentPathCheck 12
    && tttLargeFiber10Block1Chunk3ParentPathCheck 13
    && tttLargeFiber10Block1Chunk3ParentPathCheck 14
    && tttLargeFiber10Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber10Block1Chunk3ParentsAudit_ok :
    tttLargeFiber10Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber10Block1Chunk3ParentsAudit,
    tttLargeFiber10Block1Chunk3ParentPath_0_ok,
    tttLargeFiber10Block1Chunk3ParentPath_1_ok,
    tttLargeFiber10Block1Chunk3ParentPath_2_ok,
    tttLargeFiber10Block1Chunk3ParentPath_3_ok,
    tttLargeFiber10Block1Chunk3ParentPath_4_ok,
    tttLargeFiber10Block1Chunk3ParentPath_5_ok,
    tttLargeFiber10Block1Chunk3ParentPath_6_ok,
    tttLargeFiber10Block1Chunk3ParentPath_7_ok,
    tttLargeFiber10Block1Chunk3ParentPath_8_ok,
    tttLargeFiber10Block1Chunk3ParentPath_9_ok,
    tttLargeFiber10Block1Chunk3ParentPath_10_ok,
    tttLargeFiber10Block1Chunk3ParentPath_11_ok,
    tttLargeFiber10Block1Chunk3ParentPath_12_ok,
    tttLargeFiber10Block1Chunk3ParentPath_13_ok,
    tttLargeFiber10Block1Chunk3ParentPath_14_ok,
    tttLargeFiber10Block1Chunk3ParentPath_15_ok]

def tttLargeFiber10Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block1Chunk3SourcesCheck &&
    tttLargeFiber10Block1Chunk3RowsAudit &&
    tttLargeFiber10Block1Chunk3ParentMapAudit &&
    tttLargeFiber10Block1Chunk3ParentsAudit

theorem tttLargeFiber10Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber10Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block1Chunk3SourcesCheck_ok,
    tttLargeFiber10Block1Chunk3RowsAudit_ok,
    tttLargeFiber10Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber10Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
