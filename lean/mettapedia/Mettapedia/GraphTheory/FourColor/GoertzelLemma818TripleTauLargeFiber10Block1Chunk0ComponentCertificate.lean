import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block1Chunk0Sources : List Nat :=
  [   2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519,
   2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]

def tttLargeFiber10Row64 : TripleComponentParentRow :=
  tripleRow 2512 2448 73 88 80 72 80 80
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row65 : TripleComponentParentRow :=
  tripleRow 2513 2449 73 88 81 72 80 81
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row66 : TripleComponentParentRow :=
  tripleRow 2514 2450 73 88 82 72 80 82
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row67 : TripleComponentParentRow :=
  tripleRow 2515 2451 73 88 83 72 80 83
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row68 : TripleComponentParentRow :=
  tripleRow 2516 2452 73 88 100 72 80 100
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row69 : TripleComponentParentRow :=
  tripleRow 2517 2453 73 88 101 72 80 101
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row70 : TripleComponentParentRow :=
  tripleRow 2518 2454 73 88 102 72 80 102
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row71 : TripleComponentParentRow :=
  tripleRow 2519 2455 73 88 103 72 80 103
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row72 : TripleComponentParentRow :=
  tripleRow 2520 2456 73 89 88 72 81 88
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row73 : TripleComponentParentRow :=
  tripleRow 2521 2457 73 89 89 72 81 89
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row74 : TripleComponentParentRow :=
  tripleRow 2522 2458 73 89 90 72 81 90
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row75 : TripleComponentParentRow :=
  tripleRow 2523 2459 73 89 91 72 81 91
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row76 : TripleComponentParentRow :=
  tripleRow 2524 2460 73 89 108 72 81 108
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row77 : TripleComponentParentRow :=
  tripleRow 2525 2461 73 89 109 72 81 109
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row78 : TripleComponentParentRow :=
  tripleRow 2526 2462 73 89 110 72 81 110
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Row79 : TripleComponentParentRow :=
  tripleRow 2527 2463 73 89 111 72 81 111
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber10Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row64
  , tttLargeFiber10Row65
  , tttLargeFiber10Row66
  , tttLargeFiber10Row67
  , tttLargeFiber10Row68
  , tttLargeFiber10Row69
  , tttLargeFiber10Row70
  , tttLargeFiber10Row71
  , tttLargeFiber10Row72
  , tttLargeFiber10Row73
  , tttLargeFiber10Row74
  , tttLargeFiber10Row75
  , tttLargeFiber10Row76
  , tttLargeFiber10Row77
  , tttLargeFiber10Row78
  , tttLargeFiber10Row79
  ]

def tttLargeFiber10Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber10Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber10Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber10Block1Chunk0Sources

theorem tttLargeFiber10Block1Chunk0SourcesCheck_ok :
    tttLargeFiber10Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber10Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block1Chunk0RowValid
    (listGetD tttLargeFiber10Block1Chunk0Rows i default)

def tttLargeFiber10Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block1Chunk0Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block1Chunk0Sources 0 0 == 2512
      && tttLargeFiber10ParentOf 2512 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (1 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block1Chunk0Sources 1 0 == 2513
      && tttLargeFiber10ParentOf 2513 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block1Chunk0Sources 2 0 == 2514
      && tttLargeFiber10ParentOf 2514 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block1Chunk0Sources 3 0 == 2515
      && tttLargeFiber10ParentOf 2515 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block1Chunk0Sources 4 0 == 2516
      && tttLargeFiber10ParentOf 2516 == 2452
      && tttLargeFiber10ParentOf 2452 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block1Chunk0Sources 5 0 == 2517
      && tttLargeFiber10ParentOf 2517 == 2453
      && tttLargeFiber10ParentOf 2453 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block1Chunk0Sources 6 0 == 2518
      && tttLargeFiber10ParentOf 2518 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block1Chunk0Sources 7 0 == 2519
      && tttLargeFiber10ParentOf 2519 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block1Chunk0Sources 8 0 == 2520
      && tttLargeFiber10ParentOf 2520 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block1Chunk0Sources 9 0 == 2521
      && tttLargeFiber10ParentOf 2521 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block1Chunk0Sources 10 0 == 2522
      && tttLargeFiber10ParentOf 2522 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block1Chunk0Sources 11 0 == 2523
      && tttLargeFiber10ParentOf 2523 == 2459
      && tttLargeFiber10ParentOf 2459 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block1Chunk0Sources 12 0 == 2524
      && tttLargeFiber10ParentOf 2524 == 2460
      && tttLargeFiber10ParentOf 2460 == 2452
      && tttLargeFiber10ParentOf 2452 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block1Chunk0Sources 13 0 == 2525
      && tttLargeFiber10ParentOf 2525 == 2461
      && tttLargeFiber10ParentOf 2461 == 2453
      && tttLargeFiber10ParentOf 2453 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block1Chunk0Sources 14 0 == 2526
      && tttLargeFiber10ParentOf 2526 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block1Chunk0Sources 15 0 == 2527
      && tttLargeFiber10ParentOf 2527 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block1Chunk0Row_0_ok :
    tttLargeFiber10Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_1_ok :
    tttLargeFiber10Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_2_ok :
    tttLargeFiber10Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_3_ok :
    tttLargeFiber10Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_4_ok :
    tttLargeFiber10Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_5_ok :
    tttLargeFiber10Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_6_ok :
    tttLargeFiber10Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_7_ok :
    tttLargeFiber10Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_8_ok :
    tttLargeFiber10Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_9_ok :
    tttLargeFiber10Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_10_ok :
    tttLargeFiber10Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_11_ok :
    tttLargeFiber10Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_12_ok :
    tttLargeFiber10Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_13_ok :
    tttLargeFiber10Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_14_ok :
    tttLargeFiber10Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0Row_15_ok :
    tttLargeFiber10Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_0_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_1_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_2_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_3_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_4_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_5_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_6_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_7_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_8_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_9_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_10_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_11_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_12_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_13_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_14_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentMap_15_ok :
    tttLargeFiber10Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_0_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_1_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_2_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_3_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_4_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_5_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_6_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_7_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_8_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_9_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_10_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_11_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_12_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_13_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_14_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block1Chunk0ParentPath_15_ok :
    tttLargeFiber10Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber10Block1Chunk0RowCheck 0
    && tttLargeFiber10Block1Chunk0RowCheck 1
    && tttLargeFiber10Block1Chunk0RowCheck 2
    && tttLargeFiber10Block1Chunk0RowCheck 3
    && tttLargeFiber10Block1Chunk0RowCheck 4
    && tttLargeFiber10Block1Chunk0RowCheck 5
    && tttLargeFiber10Block1Chunk0RowCheck 6
    && tttLargeFiber10Block1Chunk0RowCheck 7
    && tttLargeFiber10Block1Chunk0RowCheck 8
    && tttLargeFiber10Block1Chunk0RowCheck 9
    && tttLargeFiber10Block1Chunk0RowCheck 10
    && tttLargeFiber10Block1Chunk0RowCheck 11
    && tttLargeFiber10Block1Chunk0RowCheck 12
    && tttLargeFiber10Block1Chunk0RowCheck 13
    && tttLargeFiber10Block1Chunk0RowCheck 14
    && tttLargeFiber10Block1Chunk0RowCheck 15

theorem tttLargeFiber10Block1Chunk0RowsAudit_ok :
    tttLargeFiber10Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber10Block1Chunk0RowsAudit,
    tttLargeFiber10Block1Chunk0Row_0_ok,
    tttLargeFiber10Block1Chunk0Row_1_ok,
    tttLargeFiber10Block1Chunk0Row_2_ok,
    tttLargeFiber10Block1Chunk0Row_3_ok,
    tttLargeFiber10Block1Chunk0Row_4_ok,
    tttLargeFiber10Block1Chunk0Row_5_ok,
    tttLargeFiber10Block1Chunk0Row_6_ok,
    tttLargeFiber10Block1Chunk0Row_7_ok,
    tttLargeFiber10Block1Chunk0Row_8_ok,
    tttLargeFiber10Block1Chunk0Row_9_ok,
    tttLargeFiber10Block1Chunk0Row_10_ok,
    tttLargeFiber10Block1Chunk0Row_11_ok,
    tttLargeFiber10Block1Chunk0Row_12_ok,
    tttLargeFiber10Block1Chunk0Row_13_ok,
    tttLargeFiber10Block1Chunk0Row_14_ok,
    tttLargeFiber10Block1Chunk0Row_15_ok]

def tttLargeFiber10Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber10Block1Chunk0ParentMapCheck 0
    && tttLargeFiber10Block1Chunk0ParentMapCheck 1
    && tttLargeFiber10Block1Chunk0ParentMapCheck 2
    && tttLargeFiber10Block1Chunk0ParentMapCheck 3
    && tttLargeFiber10Block1Chunk0ParentMapCheck 4
    && tttLargeFiber10Block1Chunk0ParentMapCheck 5
    && tttLargeFiber10Block1Chunk0ParentMapCheck 6
    && tttLargeFiber10Block1Chunk0ParentMapCheck 7
    && tttLargeFiber10Block1Chunk0ParentMapCheck 8
    && tttLargeFiber10Block1Chunk0ParentMapCheck 9
    && tttLargeFiber10Block1Chunk0ParentMapCheck 10
    && tttLargeFiber10Block1Chunk0ParentMapCheck 11
    && tttLargeFiber10Block1Chunk0ParentMapCheck 12
    && tttLargeFiber10Block1Chunk0ParentMapCheck 13
    && tttLargeFiber10Block1Chunk0ParentMapCheck 14
    && tttLargeFiber10Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber10Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber10Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber10Block1Chunk0ParentMapAudit,
    tttLargeFiber10Block1Chunk0ParentMap_0_ok,
    tttLargeFiber10Block1Chunk0ParentMap_1_ok,
    tttLargeFiber10Block1Chunk0ParentMap_2_ok,
    tttLargeFiber10Block1Chunk0ParentMap_3_ok,
    tttLargeFiber10Block1Chunk0ParentMap_4_ok,
    tttLargeFiber10Block1Chunk0ParentMap_5_ok,
    tttLargeFiber10Block1Chunk0ParentMap_6_ok,
    tttLargeFiber10Block1Chunk0ParentMap_7_ok,
    tttLargeFiber10Block1Chunk0ParentMap_8_ok,
    tttLargeFiber10Block1Chunk0ParentMap_9_ok,
    tttLargeFiber10Block1Chunk0ParentMap_10_ok,
    tttLargeFiber10Block1Chunk0ParentMap_11_ok,
    tttLargeFiber10Block1Chunk0ParentMap_12_ok,
    tttLargeFiber10Block1Chunk0ParentMap_13_ok,
    tttLargeFiber10Block1Chunk0ParentMap_14_ok,
    tttLargeFiber10Block1Chunk0ParentMap_15_ok]

def tttLargeFiber10Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber10Block1Chunk0ParentPathCheck 0
    && tttLargeFiber10Block1Chunk0ParentPathCheck 1
    && tttLargeFiber10Block1Chunk0ParentPathCheck 2
    && tttLargeFiber10Block1Chunk0ParentPathCheck 3
    && tttLargeFiber10Block1Chunk0ParentPathCheck 4
    && tttLargeFiber10Block1Chunk0ParentPathCheck 5
    && tttLargeFiber10Block1Chunk0ParentPathCheck 6
    && tttLargeFiber10Block1Chunk0ParentPathCheck 7
    && tttLargeFiber10Block1Chunk0ParentPathCheck 8
    && tttLargeFiber10Block1Chunk0ParentPathCheck 9
    && tttLargeFiber10Block1Chunk0ParentPathCheck 10
    && tttLargeFiber10Block1Chunk0ParentPathCheck 11
    && tttLargeFiber10Block1Chunk0ParentPathCheck 12
    && tttLargeFiber10Block1Chunk0ParentPathCheck 13
    && tttLargeFiber10Block1Chunk0ParentPathCheck 14
    && tttLargeFiber10Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber10Block1Chunk0ParentsAudit_ok :
    tttLargeFiber10Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber10Block1Chunk0ParentsAudit,
    tttLargeFiber10Block1Chunk0ParentPath_0_ok,
    tttLargeFiber10Block1Chunk0ParentPath_1_ok,
    tttLargeFiber10Block1Chunk0ParentPath_2_ok,
    tttLargeFiber10Block1Chunk0ParentPath_3_ok,
    tttLargeFiber10Block1Chunk0ParentPath_4_ok,
    tttLargeFiber10Block1Chunk0ParentPath_5_ok,
    tttLargeFiber10Block1Chunk0ParentPath_6_ok,
    tttLargeFiber10Block1Chunk0ParentPath_7_ok,
    tttLargeFiber10Block1Chunk0ParentPath_8_ok,
    tttLargeFiber10Block1Chunk0ParentPath_9_ok,
    tttLargeFiber10Block1Chunk0ParentPath_10_ok,
    tttLargeFiber10Block1Chunk0ParentPath_11_ok,
    tttLargeFiber10Block1Chunk0ParentPath_12_ok,
    tttLargeFiber10Block1Chunk0ParentPath_13_ok,
    tttLargeFiber10Block1Chunk0ParentPath_14_ok,
    tttLargeFiber10Block1Chunk0ParentPath_15_ok]

def tttLargeFiber10Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block1Chunk0SourcesCheck &&
    tttLargeFiber10Block1Chunk0RowsAudit &&
    tttLargeFiber10Block1Chunk0ParentMapAudit &&
    tttLargeFiber10Block1Chunk0ParentsAudit

theorem tttLargeFiber10Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber10Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block1Chunk0SourcesCheck_ok,
    tttLargeFiber10Block1Chunk0RowsAudit_ok,
    tttLargeFiber10Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber10Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
