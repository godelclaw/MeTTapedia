import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block1Chunk2Sources : List Nat :=
  [   2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551,
   2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]

def tttLargeFiber10Row96 : TripleComponentParentRow :=
  tripleRow 2544 2480 73 108 132 72 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row97 : TripleComponentParentRow :=
  tripleRow 2545 2481 73 108 133 72 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row98 : TripleComponentParentRow :=
  tripleRow 2546 2482 73 108 134 72 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row99 : TripleComponentParentRow :=
  tripleRow 2547 2483 73 108 135 72 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row100 : TripleComponentParentRow :=
  tripleRow 2548 2484 73 108 180 72 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row101 : TripleComponentParentRow :=
  tripleRow 2549 2485 73 108 181 72 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row102 : TripleComponentParentRow :=
  tripleRow 2550 2486 73 108 182 72 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row103 : TripleComponentParentRow :=
  tripleRow 2551 2487 73 108 183 72 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row104 : TripleComponentParentRow :=
  tripleRow 2552 2488 73 109 140 72 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row105 : TripleComponentParentRow :=
  tripleRow 2553 2489 73 109 141 72 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row106 : TripleComponentParentRow :=
  tripleRow 2554 2490 73 109 142 72 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row107 : TripleComponentParentRow :=
  tripleRow 2555 2491 73 109 143 72 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row108 : TripleComponentParentRow :=
  tripleRow 2556 2492 73 109 188 72 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row109 : TripleComponentParentRow :=
  tripleRow 2557 2493 73 109 189 72 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row110 : TripleComponentParentRow :=
  tripleRow 2558 2494 73 109 190 72 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row111 : TripleComponentParentRow :=
  tripleRow 2559 2495 73 109 191 72 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row96
  , tttLargeFiber10Row97
  , tttLargeFiber10Row98
  , tttLargeFiber10Row99
  , tttLargeFiber10Row100
  , tttLargeFiber10Row101
  , tttLargeFiber10Row102
  , tttLargeFiber10Row103
  , tttLargeFiber10Row104
  , tttLargeFiber10Row105
  , tttLargeFiber10Row106
  , tttLargeFiber10Row107
  , tttLargeFiber10Row108
  , tttLargeFiber10Row109
  , tttLargeFiber10Row110
  , tttLargeFiber10Row111
  ]

def tttLargeFiber10Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber10Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber10Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber10Block1Chunk2Sources

theorem tttLargeFiber10Block1Chunk2SourcesCheck_ok :
    tttLargeFiber10Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber10Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block1Chunk2RowValid
    (listGetD tttLargeFiber10Block1Chunk2Rows i default)

def tttLargeFiber10Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block1Chunk2Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block1Chunk2Sources 0 0 == 2544
      && tttLargeFiber10ParentOf 2544 == 2480
      && tttLargeFiber10ParentOf 2480 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block1Chunk2Sources 1 0 == 2545
      && tttLargeFiber10ParentOf 2545 == 2481
      && tttLargeFiber10ParentOf 2481 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block1Chunk2Sources 2 0 == 2546
      && tttLargeFiber10ParentOf 2546 == 2482
      && tttLargeFiber10ParentOf 2482 == 2470
      && tttLargeFiber10ParentOf 2470 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block1Chunk2Sources 3 0 == 2547
      && tttLargeFiber10ParentOf 2547 == 2483
      && tttLargeFiber10ParentOf 2483 == 2471
      && tttLargeFiber10ParentOf 2471 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block1Chunk2Sources 4 0 == 2548
      && tttLargeFiber10ParentOf 2548 == 2484
      && tttLargeFiber10ParentOf 2484 == 2466
      && tttLargeFiber10ParentOf 2466 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block1Chunk2Sources 5 0 == 2549
      && tttLargeFiber10ParentOf 2549 == 2485
      && tttLargeFiber10ParentOf 2485 == 2487
      && tttLargeFiber10ParentOf 2487 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block1Chunk2Sources 6 0 == 2550
      && tttLargeFiber10ParentOf 2550 == 2486
      && tttLargeFiber10ParentOf 2486 == 2465
      && tttLargeFiber10ParentOf 2465 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block1Chunk2Sources 7 0 == 2551
      && tttLargeFiber10ParentOf 2551 == 2487
      && tttLargeFiber10ParentOf 2487 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block1Chunk2Sources 8 0 == 2552
      && tttLargeFiber10ParentOf 2552 == 2488
      && tttLargeFiber10ParentOf 2488 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block1Chunk2Sources 9 0 == 2553
      && tttLargeFiber10ParentOf 2553 == 2489
      && tttLargeFiber10ParentOf 2489 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block1Chunk2Sources 10 0 == 2554
      && tttLargeFiber10ParentOf 2554 == 2490
      && tttLargeFiber10ParentOf 2490 == 2506
      && tttLargeFiber10ParentOf 2506 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block1Chunk2Sources 11 0 == 2555
      && tttLargeFiber10ParentOf 2555 == 2491
      && tttLargeFiber10ParentOf 2491 == 2488
      && tttLargeFiber10ParentOf 2488 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block1Chunk2Sources 12 0 == 2556
      && tttLargeFiber10ParentOf 2556 == 2492
      && tttLargeFiber10ParentOf 2492 == 2488
      && tttLargeFiber10ParentOf 2488 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block1Chunk2Sources 13 0 == 2557
      && tttLargeFiber10ParentOf 2557 == 2493
      && tttLargeFiber10ParentOf 2493 == 2489
      && tttLargeFiber10ParentOf 2489 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block1Chunk2Sources 14 0 == 2558
      && tttLargeFiber10ParentOf 2558 == 2494
      && tttLargeFiber10ParentOf 2494 == 2510
      && tttLargeFiber10ParentOf 2510 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block1Chunk2Sources 15 0 == 2559
      && tttLargeFiber10ParentOf 2559 == 2495
      && tttLargeFiber10ParentOf 2495 == 2511
      && tttLargeFiber10ParentOf 2511 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block1Chunk2Row_0_ok :
    tttLargeFiber10Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_1_ok :
    tttLargeFiber10Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_2_ok :
    tttLargeFiber10Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_3_ok :
    tttLargeFiber10Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_4_ok :
    tttLargeFiber10Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_5_ok :
    tttLargeFiber10Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_6_ok :
    tttLargeFiber10Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_7_ok :
    tttLargeFiber10Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_8_ok :
    tttLargeFiber10Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_9_ok :
    tttLargeFiber10Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_10_ok :
    tttLargeFiber10Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_11_ok :
    tttLargeFiber10Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_12_ok :
    tttLargeFiber10Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_13_ok :
    tttLargeFiber10Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_14_ok :
    tttLargeFiber10Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2Row_15_ok :
    tttLargeFiber10Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_0_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_1_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_2_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_3_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_4_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_5_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_6_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_7_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_8_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_9_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_10_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_11_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_12_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_13_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_14_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentMap_15_ok :
    tttLargeFiber10Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_0_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_1_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_2_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_3_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_4_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_5_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_6_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_7_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_8_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_9_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_10_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_11_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_12_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_13_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_14_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk2ParentPath_15_ok :
    tttLargeFiber10Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber10Block1Chunk2RowCheck 0
    && tttLargeFiber10Block1Chunk2RowCheck 1
    && tttLargeFiber10Block1Chunk2RowCheck 2
    && tttLargeFiber10Block1Chunk2RowCheck 3
    && tttLargeFiber10Block1Chunk2RowCheck 4
    && tttLargeFiber10Block1Chunk2RowCheck 5
    && tttLargeFiber10Block1Chunk2RowCheck 6
    && tttLargeFiber10Block1Chunk2RowCheck 7
    && tttLargeFiber10Block1Chunk2RowCheck 8
    && tttLargeFiber10Block1Chunk2RowCheck 9
    && tttLargeFiber10Block1Chunk2RowCheck 10
    && tttLargeFiber10Block1Chunk2RowCheck 11
    && tttLargeFiber10Block1Chunk2RowCheck 12
    && tttLargeFiber10Block1Chunk2RowCheck 13
    && tttLargeFiber10Block1Chunk2RowCheck 14
    && tttLargeFiber10Block1Chunk2RowCheck 15

theorem tttLargeFiber10Block1Chunk2RowsAudit_ok :
    tttLargeFiber10Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber10Block1Chunk2RowsAudit,
    tttLargeFiber10Block1Chunk2Row_0_ok,
    tttLargeFiber10Block1Chunk2Row_1_ok,
    tttLargeFiber10Block1Chunk2Row_2_ok,
    tttLargeFiber10Block1Chunk2Row_3_ok,
    tttLargeFiber10Block1Chunk2Row_4_ok,
    tttLargeFiber10Block1Chunk2Row_5_ok,
    tttLargeFiber10Block1Chunk2Row_6_ok,
    tttLargeFiber10Block1Chunk2Row_7_ok,
    tttLargeFiber10Block1Chunk2Row_8_ok,
    tttLargeFiber10Block1Chunk2Row_9_ok,
    tttLargeFiber10Block1Chunk2Row_10_ok,
    tttLargeFiber10Block1Chunk2Row_11_ok,
    tttLargeFiber10Block1Chunk2Row_12_ok,
    tttLargeFiber10Block1Chunk2Row_13_ok,
    tttLargeFiber10Block1Chunk2Row_14_ok,
    tttLargeFiber10Block1Chunk2Row_15_ok]

def tttLargeFiber10Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber10Block1Chunk2ParentMapCheck 0
    && tttLargeFiber10Block1Chunk2ParentMapCheck 1
    && tttLargeFiber10Block1Chunk2ParentMapCheck 2
    && tttLargeFiber10Block1Chunk2ParentMapCheck 3
    && tttLargeFiber10Block1Chunk2ParentMapCheck 4
    && tttLargeFiber10Block1Chunk2ParentMapCheck 5
    && tttLargeFiber10Block1Chunk2ParentMapCheck 6
    && tttLargeFiber10Block1Chunk2ParentMapCheck 7
    && tttLargeFiber10Block1Chunk2ParentMapCheck 8
    && tttLargeFiber10Block1Chunk2ParentMapCheck 9
    && tttLargeFiber10Block1Chunk2ParentMapCheck 10
    && tttLargeFiber10Block1Chunk2ParentMapCheck 11
    && tttLargeFiber10Block1Chunk2ParentMapCheck 12
    && tttLargeFiber10Block1Chunk2ParentMapCheck 13
    && tttLargeFiber10Block1Chunk2ParentMapCheck 14
    && tttLargeFiber10Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber10Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber10Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber10Block1Chunk2ParentMapAudit,
    tttLargeFiber10Block1Chunk2ParentMap_0_ok,
    tttLargeFiber10Block1Chunk2ParentMap_1_ok,
    tttLargeFiber10Block1Chunk2ParentMap_2_ok,
    tttLargeFiber10Block1Chunk2ParentMap_3_ok,
    tttLargeFiber10Block1Chunk2ParentMap_4_ok,
    tttLargeFiber10Block1Chunk2ParentMap_5_ok,
    tttLargeFiber10Block1Chunk2ParentMap_6_ok,
    tttLargeFiber10Block1Chunk2ParentMap_7_ok,
    tttLargeFiber10Block1Chunk2ParentMap_8_ok,
    tttLargeFiber10Block1Chunk2ParentMap_9_ok,
    tttLargeFiber10Block1Chunk2ParentMap_10_ok,
    tttLargeFiber10Block1Chunk2ParentMap_11_ok,
    tttLargeFiber10Block1Chunk2ParentMap_12_ok,
    tttLargeFiber10Block1Chunk2ParentMap_13_ok,
    tttLargeFiber10Block1Chunk2ParentMap_14_ok,
    tttLargeFiber10Block1Chunk2ParentMap_15_ok]

def tttLargeFiber10Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber10Block1Chunk2ParentPathCheck 0
    && tttLargeFiber10Block1Chunk2ParentPathCheck 1
    && tttLargeFiber10Block1Chunk2ParentPathCheck 2
    && tttLargeFiber10Block1Chunk2ParentPathCheck 3
    && tttLargeFiber10Block1Chunk2ParentPathCheck 4
    && tttLargeFiber10Block1Chunk2ParentPathCheck 5
    && tttLargeFiber10Block1Chunk2ParentPathCheck 6
    && tttLargeFiber10Block1Chunk2ParentPathCheck 7
    && tttLargeFiber10Block1Chunk2ParentPathCheck 8
    && tttLargeFiber10Block1Chunk2ParentPathCheck 9
    && tttLargeFiber10Block1Chunk2ParentPathCheck 10
    && tttLargeFiber10Block1Chunk2ParentPathCheck 11
    && tttLargeFiber10Block1Chunk2ParentPathCheck 12
    && tttLargeFiber10Block1Chunk2ParentPathCheck 13
    && tttLargeFiber10Block1Chunk2ParentPathCheck 14
    && tttLargeFiber10Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber10Block1Chunk2ParentsAudit_ok :
    tttLargeFiber10Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber10Block1Chunk2ParentsAudit,
    tttLargeFiber10Block1Chunk2ParentPath_0_ok,
    tttLargeFiber10Block1Chunk2ParentPath_1_ok,
    tttLargeFiber10Block1Chunk2ParentPath_2_ok,
    tttLargeFiber10Block1Chunk2ParentPath_3_ok,
    tttLargeFiber10Block1Chunk2ParentPath_4_ok,
    tttLargeFiber10Block1Chunk2ParentPath_5_ok,
    tttLargeFiber10Block1Chunk2ParentPath_6_ok,
    tttLargeFiber10Block1Chunk2ParentPath_7_ok,
    tttLargeFiber10Block1Chunk2ParentPath_8_ok,
    tttLargeFiber10Block1Chunk2ParentPath_9_ok,
    tttLargeFiber10Block1Chunk2ParentPath_10_ok,
    tttLargeFiber10Block1Chunk2ParentPath_11_ok,
    tttLargeFiber10Block1Chunk2ParentPath_12_ok,
    tttLargeFiber10Block1Chunk2ParentPath_13_ok,
    tttLargeFiber10Block1Chunk2ParentPath_14_ok,
    tttLargeFiber10Block1Chunk2ParentPath_15_ok]

def tttLargeFiber10Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block1Chunk2SourcesCheck &&
    tttLargeFiber10Block1Chunk2RowsAudit &&
    tttLargeFiber10Block1Chunk2ParentMapAudit &&
    tttLargeFiber10Block1Chunk2ParentsAudit

theorem tttLargeFiber10Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber10Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block1Chunk2SourcesCheck_ok,
    tttLargeFiber10Block1Chunk2RowsAudit_ok,
    tttLargeFiber10Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber10Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
