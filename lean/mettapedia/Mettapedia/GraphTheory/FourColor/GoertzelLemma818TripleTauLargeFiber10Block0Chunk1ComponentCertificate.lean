import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block0Chunk1Sources : List Nat :=
  [   2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471,
   2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]

def tttLargeFiber10Row16 : TripleComponentParentRow :=
  tripleRow 2464 2448 72 82 16 72 80 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row17 : TripleComponentParentRow :=
  tripleRow 2465 2449 72 82 17 72 80 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row18 : TripleComponentParentRow :=
  tripleRow 2466 2450 72 82 18 72 80 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row19 : TripleComponentParentRow :=
  tripleRow 2467 2451 72 82 19 72 80 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row20 : TripleComponentParentRow :=
  tripleRow 2468 2464 72 82 32 72 82 16
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row21 : TripleComponentParentRow :=
  tripleRow 2469 2465 72 82 33 72 82 17
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row22 : TripleComponentParentRow :=
  tripleRow 2470 2454 72 82 34 72 80 102
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row23 : TripleComponentParentRow :=
  tripleRow 2471 2455 72 82 35 72 80 103
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row24 : TripleComponentParentRow :=
  tripleRow 2472 2456 72 83 24 72 81 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row25 : TripleComponentParentRow :=
  tripleRow 2473 2457 72 83 25 72 81 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row26 : TripleComponentParentRow :=
  tripleRow 2474 2458 72 83 26 72 81 90
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row27 : TripleComponentParentRow :=
  tripleRow 2475 2459 72 83 27 72 81 91
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row28 : TripleComponentParentRow :=
  tripleRow 2476 2472 72 83 40 72 83 24
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row29 : TripleComponentParentRow :=
  tripleRow 2477 2473 72 83 41 72 83 25
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row30 : TripleComponentParentRow :=
  tripleRow 2478 2462 72 83 42 72 81 110
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row31 : TripleComponentParentRow :=
  tripleRow 2479 2463 72 83 43 72 81 111
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row16
  , tttLargeFiber10Row17
  , tttLargeFiber10Row18
  , tttLargeFiber10Row19
  , tttLargeFiber10Row20
  , tttLargeFiber10Row21
  , tttLargeFiber10Row22
  , tttLargeFiber10Row23
  , tttLargeFiber10Row24
  , tttLargeFiber10Row25
  , tttLargeFiber10Row26
  , tttLargeFiber10Row27
  , tttLargeFiber10Row28
  , tttLargeFiber10Row29
  , tttLargeFiber10Row30
  , tttLargeFiber10Row31
  ]

def tttLargeFiber10Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber10Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber10Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber10Block0Chunk1Sources

theorem tttLargeFiber10Block0Chunk1SourcesCheck_ok :
    tttLargeFiber10Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber10Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block0Chunk1RowValid
    (listGetD tttLargeFiber10Block0Chunk1Rows i default)

def tttLargeFiber10Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block0Chunk1Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block0Chunk1Sources 0 0 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (1 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block0Chunk1Sources 1 0 == 2465
      && tttLargeFiber10ParentOf 2465 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block0Chunk1Sources 2 0 == 2466
      && tttLargeFiber10ParentOf 2466 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block0Chunk1Sources 3 0 == 2467
      && tttLargeFiber10ParentOf 2467 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block0Chunk1Sources 4 0 == 2468
      && tttLargeFiber10ParentOf 2468 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block0Chunk1Sources 5 0 == 2469
      && tttLargeFiber10ParentOf 2469 == 2465
      && tttLargeFiber10ParentOf 2465 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block0Chunk1Sources 6 0 == 2470
      && tttLargeFiber10ParentOf 2470 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block0Chunk1Sources 7 0 == 2471
      && tttLargeFiber10ParentOf 2471 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block0Chunk1Sources 8 0 == 2472
      && tttLargeFiber10ParentOf 2472 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block0Chunk1Sources 9 0 == 2473
      && tttLargeFiber10ParentOf 2473 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block0Chunk1Sources 10 0 == 2474
      && tttLargeFiber10ParentOf 2474 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block0Chunk1Sources 11 0 == 2475
      && tttLargeFiber10ParentOf 2475 == 2459
      && tttLargeFiber10ParentOf 2459 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block0Chunk1Sources 12 0 == 2476
      && tttLargeFiber10ParentOf 2476 == 2472
      && tttLargeFiber10ParentOf 2472 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block0Chunk1Sources 13 0 == 2477
      && tttLargeFiber10ParentOf 2477 == 2473
      && tttLargeFiber10ParentOf 2473 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block0Chunk1Sources 14 0 == 2478
      && tttLargeFiber10ParentOf 2478 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block0Chunk1Sources 15 0 == 2479
      && tttLargeFiber10ParentOf 2479 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block0Chunk1Row_0_ok :
    tttLargeFiber10Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_1_ok :
    tttLargeFiber10Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_2_ok :
    tttLargeFiber10Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_3_ok :
    tttLargeFiber10Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_4_ok :
    tttLargeFiber10Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_5_ok :
    tttLargeFiber10Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_6_ok :
    tttLargeFiber10Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_7_ok :
    tttLargeFiber10Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_8_ok :
    tttLargeFiber10Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_9_ok :
    tttLargeFiber10Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_10_ok :
    tttLargeFiber10Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_11_ok :
    tttLargeFiber10Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_12_ok :
    tttLargeFiber10Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_13_ok :
    tttLargeFiber10Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_14_ok :
    tttLargeFiber10Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1Row_15_ok :
    tttLargeFiber10Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_0_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_1_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_2_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_3_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_4_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_5_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_6_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_7_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_8_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_9_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_10_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_11_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_12_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_13_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_14_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentMap_15_ok :
    tttLargeFiber10Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_0_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_1_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_2_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_3_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_4_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_5_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_6_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_7_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_8_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_9_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_10_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_11_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_12_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_13_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_14_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk1ParentPath_15_ok :
    tttLargeFiber10Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber10Block0Chunk1RowCheck 0
    && tttLargeFiber10Block0Chunk1RowCheck 1
    && tttLargeFiber10Block0Chunk1RowCheck 2
    && tttLargeFiber10Block0Chunk1RowCheck 3
    && tttLargeFiber10Block0Chunk1RowCheck 4
    && tttLargeFiber10Block0Chunk1RowCheck 5
    && tttLargeFiber10Block0Chunk1RowCheck 6
    && tttLargeFiber10Block0Chunk1RowCheck 7
    && tttLargeFiber10Block0Chunk1RowCheck 8
    && tttLargeFiber10Block0Chunk1RowCheck 9
    && tttLargeFiber10Block0Chunk1RowCheck 10
    && tttLargeFiber10Block0Chunk1RowCheck 11
    && tttLargeFiber10Block0Chunk1RowCheck 12
    && tttLargeFiber10Block0Chunk1RowCheck 13
    && tttLargeFiber10Block0Chunk1RowCheck 14
    && tttLargeFiber10Block0Chunk1RowCheck 15

theorem tttLargeFiber10Block0Chunk1RowsAudit_ok :
    tttLargeFiber10Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber10Block0Chunk1RowsAudit,
    tttLargeFiber10Block0Chunk1Row_0_ok,
    tttLargeFiber10Block0Chunk1Row_1_ok,
    tttLargeFiber10Block0Chunk1Row_2_ok,
    tttLargeFiber10Block0Chunk1Row_3_ok,
    tttLargeFiber10Block0Chunk1Row_4_ok,
    tttLargeFiber10Block0Chunk1Row_5_ok,
    tttLargeFiber10Block0Chunk1Row_6_ok,
    tttLargeFiber10Block0Chunk1Row_7_ok,
    tttLargeFiber10Block0Chunk1Row_8_ok,
    tttLargeFiber10Block0Chunk1Row_9_ok,
    tttLargeFiber10Block0Chunk1Row_10_ok,
    tttLargeFiber10Block0Chunk1Row_11_ok,
    tttLargeFiber10Block0Chunk1Row_12_ok,
    tttLargeFiber10Block0Chunk1Row_13_ok,
    tttLargeFiber10Block0Chunk1Row_14_ok,
    tttLargeFiber10Block0Chunk1Row_15_ok]

def tttLargeFiber10Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber10Block0Chunk1ParentMapCheck 0
    && tttLargeFiber10Block0Chunk1ParentMapCheck 1
    && tttLargeFiber10Block0Chunk1ParentMapCheck 2
    && tttLargeFiber10Block0Chunk1ParentMapCheck 3
    && tttLargeFiber10Block0Chunk1ParentMapCheck 4
    && tttLargeFiber10Block0Chunk1ParentMapCheck 5
    && tttLargeFiber10Block0Chunk1ParentMapCheck 6
    && tttLargeFiber10Block0Chunk1ParentMapCheck 7
    && tttLargeFiber10Block0Chunk1ParentMapCheck 8
    && tttLargeFiber10Block0Chunk1ParentMapCheck 9
    && tttLargeFiber10Block0Chunk1ParentMapCheck 10
    && tttLargeFiber10Block0Chunk1ParentMapCheck 11
    && tttLargeFiber10Block0Chunk1ParentMapCheck 12
    && tttLargeFiber10Block0Chunk1ParentMapCheck 13
    && tttLargeFiber10Block0Chunk1ParentMapCheck 14
    && tttLargeFiber10Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber10Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber10Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber10Block0Chunk1ParentMapAudit,
    tttLargeFiber10Block0Chunk1ParentMap_0_ok,
    tttLargeFiber10Block0Chunk1ParentMap_1_ok,
    tttLargeFiber10Block0Chunk1ParentMap_2_ok,
    tttLargeFiber10Block0Chunk1ParentMap_3_ok,
    tttLargeFiber10Block0Chunk1ParentMap_4_ok,
    tttLargeFiber10Block0Chunk1ParentMap_5_ok,
    tttLargeFiber10Block0Chunk1ParentMap_6_ok,
    tttLargeFiber10Block0Chunk1ParentMap_7_ok,
    tttLargeFiber10Block0Chunk1ParentMap_8_ok,
    tttLargeFiber10Block0Chunk1ParentMap_9_ok,
    tttLargeFiber10Block0Chunk1ParentMap_10_ok,
    tttLargeFiber10Block0Chunk1ParentMap_11_ok,
    tttLargeFiber10Block0Chunk1ParentMap_12_ok,
    tttLargeFiber10Block0Chunk1ParentMap_13_ok,
    tttLargeFiber10Block0Chunk1ParentMap_14_ok,
    tttLargeFiber10Block0Chunk1ParentMap_15_ok]

def tttLargeFiber10Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber10Block0Chunk1ParentPathCheck 0
    && tttLargeFiber10Block0Chunk1ParentPathCheck 1
    && tttLargeFiber10Block0Chunk1ParentPathCheck 2
    && tttLargeFiber10Block0Chunk1ParentPathCheck 3
    && tttLargeFiber10Block0Chunk1ParentPathCheck 4
    && tttLargeFiber10Block0Chunk1ParentPathCheck 5
    && tttLargeFiber10Block0Chunk1ParentPathCheck 6
    && tttLargeFiber10Block0Chunk1ParentPathCheck 7
    && tttLargeFiber10Block0Chunk1ParentPathCheck 8
    && tttLargeFiber10Block0Chunk1ParentPathCheck 9
    && tttLargeFiber10Block0Chunk1ParentPathCheck 10
    && tttLargeFiber10Block0Chunk1ParentPathCheck 11
    && tttLargeFiber10Block0Chunk1ParentPathCheck 12
    && tttLargeFiber10Block0Chunk1ParentPathCheck 13
    && tttLargeFiber10Block0Chunk1ParentPathCheck 14
    && tttLargeFiber10Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber10Block0Chunk1ParentsAudit_ok :
    tttLargeFiber10Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber10Block0Chunk1ParentsAudit,
    tttLargeFiber10Block0Chunk1ParentPath_0_ok,
    tttLargeFiber10Block0Chunk1ParentPath_1_ok,
    tttLargeFiber10Block0Chunk1ParentPath_2_ok,
    tttLargeFiber10Block0Chunk1ParentPath_3_ok,
    tttLargeFiber10Block0Chunk1ParentPath_4_ok,
    tttLargeFiber10Block0Chunk1ParentPath_5_ok,
    tttLargeFiber10Block0Chunk1ParentPath_6_ok,
    tttLargeFiber10Block0Chunk1ParentPath_7_ok,
    tttLargeFiber10Block0Chunk1ParentPath_8_ok,
    tttLargeFiber10Block0Chunk1ParentPath_9_ok,
    tttLargeFiber10Block0Chunk1ParentPath_10_ok,
    tttLargeFiber10Block0Chunk1ParentPath_11_ok,
    tttLargeFiber10Block0Chunk1ParentPath_12_ok,
    tttLargeFiber10Block0Chunk1ParentPath_13_ok,
    tttLargeFiber10Block0Chunk1ParentPath_14_ok,
    tttLargeFiber10Block0Chunk1ParentPath_15_ok]

def tttLargeFiber10Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block0Chunk1SourcesCheck &&
    tttLargeFiber10Block0Chunk1RowsAudit &&
    tttLargeFiber10Block0Chunk1ParentMapAudit &&
    tttLargeFiber10Block0Chunk1ParentsAudit

theorem tttLargeFiber10Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber10Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block0Chunk1SourcesCheck_ok,
    tttLargeFiber10Block0Chunk1RowsAudit_ok,
    tttLargeFiber10Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber10Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
