import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 0 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block0Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block0Chunk2Sources : List Nat :=
  [   2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487,
   2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]

def tttLargeFiber10Row32 : TripleComponentParentRow :=
  tripleRow 2480 2496 72 100 132 72 102 64
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

def tttLargeFiber10Row33 : TripleComponentParentRow :=
  tripleRow 2481 2497 72 100 133 72 102 65
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

def tttLargeFiber10Row34 : TripleComponentParentRow :=
  tripleRow 2482 2470 72 100 134 72 82 34
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row35 : TripleComponentParentRow :=
  tripleRow 2483 2471 72 100 135 72 82 35
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row36 : TripleComponentParentRow :=
  tripleRow 2484 2466 72 100 180 72 82 18
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row37 : TripleComponentParentRow :=
  tripleRow 2485 2487 72 100 181 72 100 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row38 : TripleComponentParentRow :=
  tripleRow 2486 2465 72 100 182 72 82 17
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row39 : TripleComponentParentRow :=
  tripleRow 2487 2464 72 100 183 72 82 16
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber10Row40 : TripleComponentParentRow :=
  tripleRow 2488 2504 72 101 140 72 103 72
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

def tttLargeFiber10Row41 : TripleComponentParentRow :=
  tripleRow 2489 2505 72 101 141 72 103 73
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

def tttLargeFiber10Row42 : TripleComponentParentRow :=
  tripleRow 2490 2506 72 101 142 72 103 74
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

def tttLargeFiber10Row43 : TripleComponentParentRow :=
  tripleRow 2491 2488 72 101 143 72 101 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row44 : TripleComponentParentRow :=
  tripleRow 2492 2488 72 101 188 72 101 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row45 : TripleComponentParentRow :=
  tripleRow 2493 2489 72 101 189 72 101 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row46 : TripleComponentParentRow :=
  tripleRow 2494 2510 72 101 190 72 103 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row47 : TripleComponentParentRow :=
  tripleRow 2495 2511 72 101 191 72 103 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Block0Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row32
  , tttLargeFiber10Row33
  , tttLargeFiber10Row34
  , tttLargeFiber10Row35
  , tttLargeFiber10Row36
  , tttLargeFiber10Row37
  , tttLargeFiber10Row38
  , tttLargeFiber10Row39
  , tttLargeFiber10Row40
  , tttLargeFiber10Row41
  , tttLargeFiber10Row42
  , tttLargeFiber10Row43
  , tttLargeFiber10Row44
  , tttLargeFiber10Row45
  , tttLargeFiber10Row46
  , tttLargeFiber10Row47
  ]

def tttLargeFiber10Block0Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block0Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block0Chunk2ExpectedContains row.source &&
    tttLargeFiber10Block0Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block0Chunk2SourcesCheck : Bool :=
  (tttLargeFiber10Block0Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber10Block0Chunk2Sources

theorem tttLargeFiber10Block0Chunk2SourcesCheck_ok :
    tttLargeFiber10Block0Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber10Block0Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block0Chunk2RowValid
    (listGetD tttLargeFiber10Block0Chunk2Rows i default)

def tttLargeFiber10Block0Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block0Chunk2Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block0Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block0Chunk2Sources 0 0 == 2480
      && tttLargeFiber10ParentOf 2480 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block0Chunk2Sources 1 0 == 2481
      && tttLargeFiber10ParentOf 2481 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block0Chunk2Sources 2 0 == 2482
      && tttLargeFiber10ParentOf 2482 == 2470
      && tttLargeFiber10ParentOf 2470 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block0Chunk2Sources 3 0 == 2483
      && tttLargeFiber10ParentOf 2483 == 2471
      && tttLargeFiber10ParentOf 2471 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block0Chunk2Sources 4 0 == 2484
      && tttLargeFiber10ParentOf 2484 == 2466
      && tttLargeFiber10ParentOf 2466 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block0Chunk2Sources 5 0 == 2485
      && tttLargeFiber10ParentOf 2485 == 2487
      && tttLargeFiber10ParentOf 2487 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block0Chunk2Sources 6 0 == 2486
      && tttLargeFiber10ParentOf 2486 == 2465
      && tttLargeFiber10ParentOf 2465 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block0Chunk2Sources 7 0 == 2487
      && tttLargeFiber10ParentOf 2487 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block0Chunk2Sources 8 0 == 2488
      && tttLargeFiber10ParentOf 2488 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block0Chunk2Sources 9 0 == 2489
      && tttLargeFiber10ParentOf 2489 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block0Chunk2Sources 10 0 == 2490
      && tttLargeFiber10ParentOf 2490 == 2506
      && tttLargeFiber10ParentOf 2506 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block0Chunk2Sources 11 0 == 2491
      && tttLargeFiber10ParentOf 2491 == 2488
      && tttLargeFiber10ParentOf 2488 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block0Chunk2Sources 12 0 == 2492
      && tttLargeFiber10ParentOf 2492 == 2488
      && tttLargeFiber10ParentOf 2488 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block0Chunk2Sources 13 0 == 2493
      && tttLargeFiber10ParentOf 2493 == 2489
      && tttLargeFiber10ParentOf 2489 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block0Chunk2Sources 14 0 == 2494
      && tttLargeFiber10ParentOf 2494 == 2510
      && tttLargeFiber10ParentOf 2510 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block0Chunk2Sources 15 0 == 2495
      && tttLargeFiber10ParentOf 2495 == 2511
      && tttLargeFiber10ParentOf 2511 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block0Chunk2Row_0_ok :
    tttLargeFiber10Block0Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_1_ok :
    tttLargeFiber10Block0Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_2_ok :
    tttLargeFiber10Block0Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_3_ok :
    tttLargeFiber10Block0Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_4_ok :
    tttLargeFiber10Block0Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_5_ok :
    tttLargeFiber10Block0Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_6_ok :
    tttLargeFiber10Block0Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_7_ok :
    tttLargeFiber10Block0Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_8_ok :
    tttLargeFiber10Block0Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_9_ok :
    tttLargeFiber10Block0Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_10_ok :
    tttLargeFiber10Block0Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_11_ok :
    tttLargeFiber10Block0Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_12_ok :
    tttLargeFiber10Block0Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_13_ok :
    tttLargeFiber10Block0Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_14_ok :
    tttLargeFiber10Block0Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2Row_15_ok :
    tttLargeFiber10Block0Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_0_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_1_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_2_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_3_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_4_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_5_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_6_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_7_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_8_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_9_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_10_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_11_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_12_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_13_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_14_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentMap_15_ok :
    tttLargeFiber10Block0Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_0_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_1_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_2_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_3_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_4_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_5_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_6_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_7_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_8_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_9_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_10_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_11_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_12_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_13_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_14_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk2ParentPath_15_ok :
    tttLargeFiber10Block0Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block0Chunk2RowsAudit : Bool :=
  tttLargeFiber10Block0Chunk2RowCheck 0
    && tttLargeFiber10Block0Chunk2RowCheck 1
    && tttLargeFiber10Block0Chunk2RowCheck 2
    && tttLargeFiber10Block0Chunk2RowCheck 3
    && tttLargeFiber10Block0Chunk2RowCheck 4
    && tttLargeFiber10Block0Chunk2RowCheck 5
    && tttLargeFiber10Block0Chunk2RowCheck 6
    && tttLargeFiber10Block0Chunk2RowCheck 7
    && tttLargeFiber10Block0Chunk2RowCheck 8
    && tttLargeFiber10Block0Chunk2RowCheck 9
    && tttLargeFiber10Block0Chunk2RowCheck 10
    && tttLargeFiber10Block0Chunk2RowCheck 11
    && tttLargeFiber10Block0Chunk2RowCheck 12
    && tttLargeFiber10Block0Chunk2RowCheck 13
    && tttLargeFiber10Block0Chunk2RowCheck 14
    && tttLargeFiber10Block0Chunk2RowCheck 15

theorem tttLargeFiber10Block0Chunk2RowsAudit_ok :
    tttLargeFiber10Block0Chunk2RowsAudit = true := by
  simp [tttLargeFiber10Block0Chunk2RowsAudit,
    tttLargeFiber10Block0Chunk2Row_0_ok,
    tttLargeFiber10Block0Chunk2Row_1_ok,
    tttLargeFiber10Block0Chunk2Row_2_ok,
    tttLargeFiber10Block0Chunk2Row_3_ok,
    tttLargeFiber10Block0Chunk2Row_4_ok,
    tttLargeFiber10Block0Chunk2Row_5_ok,
    tttLargeFiber10Block0Chunk2Row_6_ok,
    tttLargeFiber10Block0Chunk2Row_7_ok,
    tttLargeFiber10Block0Chunk2Row_8_ok,
    tttLargeFiber10Block0Chunk2Row_9_ok,
    tttLargeFiber10Block0Chunk2Row_10_ok,
    tttLargeFiber10Block0Chunk2Row_11_ok,
    tttLargeFiber10Block0Chunk2Row_12_ok,
    tttLargeFiber10Block0Chunk2Row_13_ok,
    tttLargeFiber10Block0Chunk2Row_14_ok,
    tttLargeFiber10Block0Chunk2Row_15_ok]

def tttLargeFiber10Block0Chunk2ParentMapAudit : Bool :=
  tttLargeFiber10Block0Chunk2ParentMapCheck 0
    && tttLargeFiber10Block0Chunk2ParentMapCheck 1
    && tttLargeFiber10Block0Chunk2ParentMapCheck 2
    && tttLargeFiber10Block0Chunk2ParentMapCheck 3
    && tttLargeFiber10Block0Chunk2ParentMapCheck 4
    && tttLargeFiber10Block0Chunk2ParentMapCheck 5
    && tttLargeFiber10Block0Chunk2ParentMapCheck 6
    && tttLargeFiber10Block0Chunk2ParentMapCheck 7
    && tttLargeFiber10Block0Chunk2ParentMapCheck 8
    && tttLargeFiber10Block0Chunk2ParentMapCheck 9
    && tttLargeFiber10Block0Chunk2ParentMapCheck 10
    && tttLargeFiber10Block0Chunk2ParentMapCheck 11
    && tttLargeFiber10Block0Chunk2ParentMapCheck 12
    && tttLargeFiber10Block0Chunk2ParentMapCheck 13
    && tttLargeFiber10Block0Chunk2ParentMapCheck 14
    && tttLargeFiber10Block0Chunk2ParentMapCheck 15

theorem tttLargeFiber10Block0Chunk2ParentMapAudit_ok :
    tttLargeFiber10Block0Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber10Block0Chunk2ParentMapAudit,
    tttLargeFiber10Block0Chunk2ParentMap_0_ok,
    tttLargeFiber10Block0Chunk2ParentMap_1_ok,
    tttLargeFiber10Block0Chunk2ParentMap_2_ok,
    tttLargeFiber10Block0Chunk2ParentMap_3_ok,
    tttLargeFiber10Block0Chunk2ParentMap_4_ok,
    tttLargeFiber10Block0Chunk2ParentMap_5_ok,
    tttLargeFiber10Block0Chunk2ParentMap_6_ok,
    tttLargeFiber10Block0Chunk2ParentMap_7_ok,
    tttLargeFiber10Block0Chunk2ParentMap_8_ok,
    tttLargeFiber10Block0Chunk2ParentMap_9_ok,
    tttLargeFiber10Block0Chunk2ParentMap_10_ok,
    tttLargeFiber10Block0Chunk2ParentMap_11_ok,
    tttLargeFiber10Block0Chunk2ParentMap_12_ok,
    tttLargeFiber10Block0Chunk2ParentMap_13_ok,
    tttLargeFiber10Block0Chunk2ParentMap_14_ok,
    tttLargeFiber10Block0Chunk2ParentMap_15_ok]

def tttLargeFiber10Block0Chunk2ParentsAudit : Bool :=
  tttLargeFiber10Block0Chunk2ParentPathCheck 0
    && tttLargeFiber10Block0Chunk2ParentPathCheck 1
    && tttLargeFiber10Block0Chunk2ParentPathCheck 2
    && tttLargeFiber10Block0Chunk2ParentPathCheck 3
    && tttLargeFiber10Block0Chunk2ParentPathCheck 4
    && tttLargeFiber10Block0Chunk2ParentPathCheck 5
    && tttLargeFiber10Block0Chunk2ParentPathCheck 6
    && tttLargeFiber10Block0Chunk2ParentPathCheck 7
    && tttLargeFiber10Block0Chunk2ParentPathCheck 8
    && tttLargeFiber10Block0Chunk2ParentPathCheck 9
    && tttLargeFiber10Block0Chunk2ParentPathCheck 10
    && tttLargeFiber10Block0Chunk2ParentPathCheck 11
    && tttLargeFiber10Block0Chunk2ParentPathCheck 12
    && tttLargeFiber10Block0Chunk2ParentPathCheck 13
    && tttLargeFiber10Block0Chunk2ParentPathCheck 14
    && tttLargeFiber10Block0Chunk2ParentPathCheck 15

theorem tttLargeFiber10Block0Chunk2ParentsAudit_ok :
    tttLargeFiber10Block0Chunk2ParentsAudit = true := by
  simp [tttLargeFiber10Block0Chunk2ParentsAudit,
    tttLargeFiber10Block0Chunk2ParentPath_0_ok,
    tttLargeFiber10Block0Chunk2ParentPath_1_ok,
    tttLargeFiber10Block0Chunk2ParentPath_2_ok,
    tttLargeFiber10Block0Chunk2ParentPath_3_ok,
    tttLargeFiber10Block0Chunk2ParentPath_4_ok,
    tttLargeFiber10Block0Chunk2ParentPath_5_ok,
    tttLargeFiber10Block0Chunk2ParentPath_6_ok,
    tttLargeFiber10Block0Chunk2ParentPath_7_ok,
    tttLargeFiber10Block0Chunk2ParentPath_8_ok,
    tttLargeFiber10Block0Chunk2ParentPath_9_ok,
    tttLargeFiber10Block0Chunk2ParentPath_10_ok,
    tttLargeFiber10Block0Chunk2ParentPath_11_ok,
    tttLargeFiber10Block0Chunk2ParentPath_12_ok,
    tttLargeFiber10Block0Chunk2ParentPath_13_ok,
    tttLargeFiber10Block0Chunk2ParentPath_14_ok,
    tttLargeFiber10Block0Chunk2ParentPath_15_ok]

def tttLargeFiber10Block0Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block0Chunk2SourcesCheck &&
    tttLargeFiber10Block0Chunk2RowsAudit &&
    tttLargeFiber10Block0Chunk2ParentMapAudit &&
    tttLargeFiber10Block0Chunk2ParentsAudit

theorem tttLargeFiber10Block0Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber10Block0Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block0Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block0Chunk2SourcesCheck_ok,
    tttLargeFiber10Block0Chunk2RowsAudit_ok,
    tttLargeFiber10Block0Chunk2ParentMapAudit_ok,
    tttLargeFiber10Block0Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block0Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
