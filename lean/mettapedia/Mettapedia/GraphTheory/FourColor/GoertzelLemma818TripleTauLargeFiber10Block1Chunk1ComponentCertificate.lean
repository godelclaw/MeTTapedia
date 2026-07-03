import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block1Chunk1Sources : List Nat :=
  [   2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535,
   2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]

def tttLargeFiber10Row80 : TripleComponentParentRow :=
  tripleRow 2528 2464 73 90 16 72 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row81 : TripleComponentParentRow :=
  tripleRow 2529 2465 73 90 17 72 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row82 : TripleComponentParentRow :=
  tripleRow 2530 2466 73 90 18 72 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row83 : TripleComponentParentRow :=
  tripleRow 2531 2467 73 90 19 72 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row84 : TripleComponentParentRow :=
  tripleRow 2532 2468 73 90 32 72 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row85 : TripleComponentParentRow :=
  tripleRow 2533 2469 73 90 33 72 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row86 : TripleComponentParentRow :=
  tripleRow 2534 2470 73 90 34 72 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row87 : TripleComponentParentRow :=
  tripleRow 2535 2471 73 90 35 72 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row88 : TripleComponentParentRow :=
  tripleRow 2536 2472 73 91 24 72 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row89 : TripleComponentParentRow :=
  tripleRow 2537 2473 73 91 25 72 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row90 : TripleComponentParentRow :=
  tripleRow 2538 2474 73 91 26 72 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row91 : TripleComponentParentRow :=
  tripleRow 2539 2475 73 91 27 72 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row92 : TripleComponentParentRow :=
  tripleRow 2540 2476 73 91 40 72 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row93 : TripleComponentParentRow :=
  tripleRow 2541 2477 73 91 41 72 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row94 : TripleComponentParentRow :=
  tripleRow 2542 2478 73 91 42 72 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row95 : TripleComponentParentRow :=
  tripleRow 2543 2479 73 91 43 72 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row80
  , tttLargeFiber10Row81
  , tttLargeFiber10Row82
  , tttLargeFiber10Row83
  , tttLargeFiber10Row84
  , tttLargeFiber10Row85
  , tttLargeFiber10Row86
  , tttLargeFiber10Row87
  , tttLargeFiber10Row88
  , tttLargeFiber10Row89
  , tttLargeFiber10Row90
  , tttLargeFiber10Row91
  , tttLargeFiber10Row92
  , tttLargeFiber10Row93
  , tttLargeFiber10Row94
  , tttLargeFiber10Row95
  ]

def tttLargeFiber10Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber10Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber10Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber10Block1Chunk1Sources

theorem tttLargeFiber10Block1Chunk1SourcesCheck_ok :
    tttLargeFiber10Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber10Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block1Chunk1RowValid
    (listGetD tttLargeFiber10Block1Chunk1Rows i default)

def tttLargeFiber10Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block1Chunk1Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block1Chunk1Sources 0 0 == 2528
      && tttLargeFiber10ParentOf 2528 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block1Chunk1Sources 1 0 == 2529
      && tttLargeFiber10ParentOf 2529 == 2465
      && tttLargeFiber10ParentOf 2465 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block1Chunk1Sources 2 0 == 2530
      && tttLargeFiber10ParentOf 2530 == 2466
      && tttLargeFiber10ParentOf 2466 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block1Chunk1Sources 3 0 == 2531
      && tttLargeFiber10ParentOf 2531 == 2467
      && tttLargeFiber10ParentOf 2467 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block1Chunk1Sources 4 0 == 2532
      && tttLargeFiber10ParentOf 2532 == 2468
      && tttLargeFiber10ParentOf 2468 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block1Chunk1Sources 5 0 == 2533
      && tttLargeFiber10ParentOf 2533 == 2469
      && tttLargeFiber10ParentOf 2469 == 2465
      && tttLargeFiber10ParentOf 2465 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block1Chunk1Sources 6 0 == 2534
      && tttLargeFiber10ParentOf 2534 == 2470
      && tttLargeFiber10ParentOf 2470 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block1Chunk1Sources 7 0 == 2535
      && tttLargeFiber10ParentOf 2535 == 2471
      && tttLargeFiber10ParentOf 2471 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block1Chunk1Sources 8 0 == 2536
      && tttLargeFiber10ParentOf 2536 == 2472
      && tttLargeFiber10ParentOf 2472 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block1Chunk1Sources 9 0 == 2537
      && tttLargeFiber10ParentOf 2537 == 2473
      && tttLargeFiber10ParentOf 2473 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block1Chunk1Sources 10 0 == 2538
      && tttLargeFiber10ParentOf 2538 == 2474
      && tttLargeFiber10ParentOf 2474 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block1Chunk1Sources 11 0 == 2539
      && tttLargeFiber10ParentOf 2539 == 2475
      && tttLargeFiber10ParentOf 2475 == 2459
      && tttLargeFiber10ParentOf 2459 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block1Chunk1Sources 12 0 == 2540
      && tttLargeFiber10ParentOf 2540 == 2476
      && tttLargeFiber10ParentOf 2476 == 2472
      && tttLargeFiber10ParentOf 2472 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block1Chunk1Sources 13 0 == 2541
      && tttLargeFiber10ParentOf 2541 == 2477
      && tttLargeFiber10ParentOf 2477 == 2473
      && tttLargeFiber10ParentOf 2473 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block1Chunk1Sources 14 0 == 2542
      && tttLargeFiber10ParentOf 2542 == 2478
      && tttLargeFiber10ParentOf 2478 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block1Chunk1Sources 15 0 == 2543
      && tttLargeFiber10ParentOf 2543 == 2479
      && tttLargeFiber10ParentOf 2479 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block1Chunk1Row_0_ok :
    tttLargeFiber10Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_1_ok :
    tttLargeFiber10Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_2_ok :
    tttLargeFiber10Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_3_ok :
    tttLargeFiber10Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_4_ok :
    tttLargeFiber10Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_5_ok :
    tttLargeFiber10Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_6_ok :
    tttLargeFiber10Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_7_ok :
    tttLargeFiber10Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_8_ok :
    tttLargeFiber10Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_9_ok :
    tttLargeFiber10Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_10_ok :
    tttLargeFiber10Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_11_ok :
    tttLargeFiber10Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_12_ok :
    tttLargeFiber10Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_13_ok :
    tttLargeFiber10Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_14_ok :
    tttLargeFiber10Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1Row_15_ok :
    tttLargeFiber10Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_0_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_1_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_2_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_3_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_4_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_5_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_6_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_7_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_8_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_9_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_10_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_11_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_12_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_13_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_14_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentMap_15_ok :
    tttLargeFiber10Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_0_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_1_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_2_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_3_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_4_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_5_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_6_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_7_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_8_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_9_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_10_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_11_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_12_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_13_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_14_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk1ParentPath_15_ok :
    tttLargeFiber10Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber10Block1Chunk1RowCheck 0
    && tttLargeFiber10Block1Chunk1RowCheck 1
    && tttLargeFiber10Block1Chunk1RowCheck 2
    && tttLargeFiber10Block1Chunk1RowCheck 3
    && tttLargeFiber10Block1Chunk1RowCheck 4
    && tttLargeFiber10Block1Chunk1RowCheck 5
    && tttLargeFiber10Block1Chunk1RowCheck 6
    && tttLargeFiber10Block1Chunk1RowCheck 7
    && tttLargeFiber10Block1Chunk1RowCheck 8
    && tttLargeFiber10Block1Chunk1RowCheck 9
    && tttLargeFiber10Block1Chunk1RowCheck 10
    && tttLargeFiber10Block1Chunk1RowCheck 11
    && tttLargeFiber10Block1Chunk1RowCheck 12
    && tttLargeFiber10Block1Chunk1RowCheck 13
    && tttLargeFiber10Block1Chunk1RowCheck 14
    && tttLargeFiber10Block1Chunk1RowCheck 15

theorem tttLargeFiber10Block1Chunk1RowsAudit_ok :
    tttLargeFiber10Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber10Block1Chunk1RowsAudit,
    tttLargeFiber10Block1Chunk1Row_0_ok,
    tttLargeFiber10Block1Chunk1Row_1_ok,
    tttLargeFiber10Block1Chunk1Row_2_ok,
    tttLargeFiber10Block1Chunk1Row_3_ok,
    tttLargeFiber10Block1Chunk1Row_4_ok,
    tttLargeFiber10Block1Chunk1Row_5_ok,
    tttLargeFiber10Block1Chunk1Row_6_ok,
    tttLargeFiber10Block1Chunk1Row_7_ok,
    tttLargeFiber10Block1Chunk1Row_8_ok,
    tttLargeFiber10Block1Chunk1Row_9_ok,
    tttLargeFiber10Block1Chunk1Row_10_ok,
    tttLargeFiber10Block1Chunk1Row_11_ok,
    tttLargeFiber10Block1Chunk1Row_12_ok,
    tttLargeFiber10Block1Chunk1Row_13_ok,
    tttLargeFiber10Block1Chunk1Row_14_ok,
    tttLargeFiber10Block1Chunk1Row_15_ok]

def tttLargeFiber10Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber10Block1Chunk1ParentMapCheck 0
    && tttLargeFiber10Block1Chunk1ParentMapCheck 1
    && tttLargeFiber10Block1Chunk1ParentMapCheck 2
    && tttLargeFiber10Block1Chunk1ParentMapCheck 3
    && tttLargeFiber10Block1Chunk1ParentMapCheck 4
    && tttLargeFiber10Block1Chunk1ParentMapCheck 5
    && tttLargeFiber10Block1Chunk1ParentMapCheck 6
    && tttLargeFiber10Block1Chunk1ParentMapCheck 7
    && tttLargeFiber10Block1Chunk1ParentMapCheck 8
    && tttLargeFiber10Block1Chunk1ParentMapCheck 9
    && tttLargeFiber10Block1Chunk1ParentMapCheck 10
    && tttLargeFiber10Block1Chunk1ParentMapCheck 11
    && tttLargeFiber10Block1Chunk1ParentMapCheck 12
    && tttLargeFiber10Block1Chunk1ParentMapCheck 13
    && tttLargeFiber10Block1Chunk1ParentMapCheck 14
    && tttLargeFiber10Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber10Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber10Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber10Block1Chunk1ParentMapAudit,
    tttLargeFiber10Block1Chunk1ParentMap_0_ok,
    tttLargeFiber10Block1Chunk1ParentMap_1_ok,
    tttLargeFiber10Block1Chunk1ParentMap_2_ok,
    tttLargeFiber10Block1Chunk1ParentMap_3_ok,
    tttLargeFiber10Block1Chunk1ParentMap_4_ok,
    tttLargeFiber10Block1Chunk1ParentMap_5_ok,
    tttLargeFiber10Block1Chunk1ParentMap_6_ok,
    tttLargeFiber10Block1Chunk1ParentMap_7_ok,
    tttLargeFiber10Block1Chunk1ParentMap_8_ok,
    tttLargeFiber10Block1Chunk1ParentMap_9_ok,
    tttLargeFiber10Block1Chunk1ParentMap_10_ok,
    tttLargeFiber10Block1Chunk1ParentMap_11_ok,
    tttLargeFiber10Block1Chunk1ParentMap_12_ok,
    tttLargeFiber10Block1Chunk1ParentMap_13_ok,
    tttLargeFiber10Block1Chunk1ParentMap_14_ok,
    tttLargeFiber10Block1Chunk1ParentMap_15_ok]

def tttLargeFiber10Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber10Block1Chunk1ParentPathCheck 0
    && tttLargeFiber10Block1Chunk1ParentPathCheck 1
    && tttLargeFiber10Block1Chunk1ParentPathCheck 2
    && tttLargeFiber10Block1Chunk1ParentPathCheck 3
    && tttLargeFiber10Block1Chunk1ParentPathCheck 4
    && tttLargeFiber10Block1Chunk1ParentPathCheck 5
    && tttLargeFiber10Block1Chunk1ParentPathCheck 6
    && tttLargeFiber10Block1Chunk1ParentPathCheck 7
    && tttLargeFiber10Block1Chunk1ParentPathCheck 8
    && tttLargeFiber10Block1Chunk1ParentPathCheck 9
    && tttLargeFiber10Block1Chunk1ParentPathCheck 10
    && tttLargeFiber10Block1Chunk1ParentPathCheck 11
    && tttLargeFiber10Block1Chunk1ParentPathCheck 12
    && tttLargeFiber10Block1Chunk1ParentPathCheck 13
    && tttLargeFiber10Block1Chunk1ParentPathCheck 14
    && tttLargeFiber10Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber10Block1Chunk1ParentsAudit_ok :
    tttLargeFiber10Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber10Block1Chunk1ParentsAudit,
    tttLargeFiber10Block1Chunk1ParentPath_0_ok,
    tttLargeFiber10Block1Chunk1ParentPath_1_ok,
    tttLargeFiber10Block1Chunk1ParentPath_2_ok,
    tttLargeFiber10Block1Chunk1ParentPath_3_ok,
    tttLargeFiber10Block1Chunk1ParentPath_4_ok,
    tttLargeFiber10Block1Chunk1ParentPath_5_ok,
    tttLargeFiber10Block1Chunk1ParentPath_6_ok,
    tttLargeFiber10Block1Chunk1ParentPath_7_ok,
    tttLargeFiber10Block1Chunk1ParentPath_8_ok,
    tttLargeFiber10Block1Chunk1ParentPath_9_ok,
    tttLargeFiber10Block1Chunk1ParentPath_10_ok,
    tttLargeFiber10Block1Chunk1ParentPath_11_ok,
    tttLargeFiber10Block1Chunk1ParentPath_12_ok,
    tttLargeFiber10Block1Chunk1ParentPath_13_ok,
    tttLargeFiber10Block1Chunk1ParentPath_14_ok,
    tttLargeFiber10Block1Chunk1ParentPath_15_ok]

def tttLargeFiber10Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block1Chunk1SourcesCheck &&
    tttLargeFiber10Block1Chunk1RowsAudit &&
    tttLargeFiber10Block1Chunk1ParentMapAudit &&
    tttLargeFiber10Block1Chunk1ParentsAudit

theorem tttLargeFiber10Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber10Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block1Chunk1SourcesCheck_ok,
    tttLargeFiber10Block1Chunk1RowsAudit_ok,
    tttLargeFiber10Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber10Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
