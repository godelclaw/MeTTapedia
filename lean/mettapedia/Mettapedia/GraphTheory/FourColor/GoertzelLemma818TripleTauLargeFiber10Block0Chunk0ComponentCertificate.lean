import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block0Chunk0Sources : List Nat :=
  [   2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455,
   2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]

def tttLargeFiber10Row0 : TripleComponentParentRow :=
  tripleRow 2448 2448 72 80 80 72 80 80
    default
    []

def tttLargeFiber10Row1 : TripleComponentParentRow :=
  tripleRow 2449 2448 72 80 81 72 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row2 : TripleComponentParentRow :=
  tripleRow 2450 2448 72 80 82 72 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row3 : TripleComponentParentRow :=
  tripleRow 2451 2449 72 80 83 72 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row4 : TripleComponentParentRow :=
  tripleRow 2452 2450 72 80 100 72 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row5 : TripleComponentParentRow :=
  tripleRow 2453 2455 72 80 101 72 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row6 : TripleComponentParentRow :=
  tripleRow 2454 2449 72 80 102 72 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row7 : TripleComponentParentRow :=
  tripleRow 2455 2448 72 80 103 72 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row8 : TripleComponentParentRow :=
  tripleRow 2456 2448 72 81 88 72 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Row9 : TripleComponentParentRow :=
  tripleRow 2457 2449 72 81 89 72 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Row10 : TripleComponentParentRow :=
  tripleRow 2458 2450 72 81 90 72 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Row11 : TripleComponentParentRow :=
  tripleRow 2459 2451 72 81 91 72 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Row12 : TripleComponentParentRow :=
  tripleRow 2460 2452 72 81 108 72 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Row13 : TripleComponentParentRow :=
  tripleRow 2461 2453 72 81 109 72 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Row14 : TripleComponentParentRow :=
  tripleRow 2462 2454 72 81 110 72 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Row15 : TripleComponentParentRow :=
  tripleRow 2463 2455 72 81 111 72 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber10Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row0
  , tttLargeFiber10Row1
  , tttLargeFiber10Row2
  , tttLargeFiber10Row3
  , tttLargeFiber10Row4
  , tttLargeFiber10Row5
  , tttLargeFiber10Row6
  , tttLargeFiber10Row7
  , tttLargeFiber10Row8
  , tttLargeFiber10Row9
  , tttLargeFiber10Row10
  , tttLargeFiber10Row11
  , tttLargeFiber10Row12
  , tttLargeFiber10Row13
  , tttLargeFiber10Row14
  , tttLargeFiber10Row15
  ]

def tttLargeFiber10Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber10Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber10Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber10Block0Chunk0Sources

theorem tttLargeFiber10Block0Chunk0SourcesCheck_ok :
    tttLargeFiber10Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber10Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block0Chunk0RowValid
    (listGetD tttLargeFiber10Block0Chunk0Rows i default)

def tttLargeFiber10Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block0Chunk0Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block0Chunk0Sources 0 0 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (0 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block0Chunk0Sources 1 0 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (1 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block0Chunk0Sources 2 0 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (1 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block0Chunk0Sources 3 0 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block0Chunk0Sources 4 0 == 2452
      && tttLargeFiber10ParentOf 2452 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block0Chunk0Sources 5 0 == 2453
      && tttLargeFiber10ParentOf 2453 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block0Chunk0Sources 6 0 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block0Chunk0Sources 7 0 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (1 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block0Chunk0Sources 8 0 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (1 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block0Chunk0Sources 9 0 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block0Chunk0Sources 10 0 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block0Chunk0Sources 11 0 == 2459
      && tttLargeFiber10ParentOf 2459 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block0Chunk0Sources 12 0 == 2460
      && tttLargeFiber10ParentOf 2460 == 2452
      && tttLargeFiber10ParentOf 2452 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block0Chunk0Sources 13 0 == 2461
      && tttLargeFiber10ParentOf 2461 == 2453
      && tttLargeFiber10ParentOf 2453 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block0Chunk0Sources 14 0 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block0Chunk0Sources 15 0 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block0Chunk0Row_0_ok :
    tttLargeFiber10Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_1_ok :
    tttLargeFiber10Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_2_ok :
    tttLargeFiber10Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_3_ok :
    tttLargeFiber10Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_4_ok :
    tttLargeFiber10Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_5_ok :
    tttLargeFiber10Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_6_ok :
    tttLargeFiber10Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_7_ok :
    tttLargeFiber10Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_8_ok :
    tttLargeFiber10Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_9_ok :
    tttLargeFiber10Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_10_ok :
    tttLargeFiber10Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_11_ok :
    tttLargeFiber10Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_12_ok :
    tttLargeFiber10Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_13_ok :
    tttLargeFiber10Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_14_ok :
    tttLargeFiber10Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0Row_15_ok :
    tttLargeFiber10Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_0_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_1_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_2_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_3_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_4_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_5_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_6_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_7_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_8_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_9_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_10_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_11_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_12_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_13_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_14_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentMap_15_ok :
    tttLargeFiber10Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_0_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_1_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_2_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_3_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_4_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_5_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_6_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_7_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_8_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_9_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_10_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_11_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_12_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_13_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_14_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block0Chunk0ParentPath_15_ok :
    tttLargeFiber10Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber10Block0Chunk0RowCheck 0
    && tttLargeFiber10Block0Chunk0RowCheck 1
    && tttLargeFiber10Block0Chunk0RowCheck 2
    && tttLargeFiber10Block0Chunk0RowCheck 3
    && tttLargeFiber10Block0Chunk0RowCheck 4
    && tttLargeFiber10Block0Chunk0RowCheck 5
    && tttLargeFiber10Block0Chunk0RowCheck 6
    && tttLargeFiber10Block0Chunk0RowCheck 7
    && tttLargeFiber10Block0Chunk0RowCheck 8
    && tttLargeFiber10Block0Chunk0RowCheck 9
    && tttLargeFiber10Block0Chunk0RowCheck 10
    && tttLargeFiber10Block0Chunk0RowCheck 11
    && tttLargeFiber10Block0Chunk0RowCheck 12
    && tttLargeFiber10Block0Chunk0RowCheck 13
    && tttLargeFiber10Block0Chunk0RowCheck 14
    && tttLargeFiber10Block0Chunk0RowCheck 15

theorem tttLargeFiber10Block0Chunk0RowsAudit_ok :
    tttLargeFiber10Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber10Block0Chunk0RowsAudit,
    tttLargeFiber10Block0Chunk0Row_0_ok,
    tttLargeFiber10Block0Chunk0Row_1_ok,
    tttLargeFiber10Block0Chunk0Row_2_ok,
    tttLargeFiber10Block0Chunk0Row_3_ok,
    tttLargeFiber10Block0Chunk0Row_4_ok,
    tttLargeFiber10Block0Chunk0Row_5_ok,
    tttLargeFiber10Block0Chunk0Row_6_ok,
    tttLargeFiber10Block0Chunk0Row_7_ok,
    tttLargeFiber10Block0Chunk0Row_8_ok,
    tttLargeFiber10Block0Chunk0Row_9_ok,
    tttLargeFiber10Block0Chunk0Row_10_ok,
    tttLargeFiber10Block0Chunk0Row_11_ok,
    tttLargeFiber10Block0Chunk0Row_12_ok,
    tttLargeFiber10Block0Chunk0Row_13_ok,
    tttLargeFiber10Block0Chunk0Row_14_ok,
    tttLargeFiber10Block0Chunk0Row_15_ok]

def tttLargeFiber10Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber10Block0Chunk0ParentMapCheck 0
    && tttLargeFiber10Block0Chunk0ParentMapCheck 1
    && tttLargeFiber10Block0Chunk0ParentMapCheck 2
    && tttLargeFiber10Block0Chunk0ParentMapCheck 3
    && tttLargeFiber10Block0Chunk0ParentMapCheck 4
    && tttLargeFiber10Block0Chunk0ParentMapCheck 5
    && tttLargeFiber10Block0Chunk0ParentMapCheck 6
    && tttLargeFiber10Block0Chunk0ParentMapCheck 7
    && tttLargeFiber10Block0Chunk0ParentMapCheck 8
    && tttLargeFiber10Block0Chunk0ParentMapCheck 9
    && tttLargeFiber10Block0Chunk0ParentMapCheck 10
    && tttLargeFiber10Block0Chunk0ParentMapCheck 11
    && tttLargeFiber10Block0Chunk0ParentMapCheck 12
    && tttLargeFiber10Block0Chunk0ParentMapCheck 13
    && tttLargeFiber10Block0Chunk0ParentMapCheck 14
    && tttLargeFiber10Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber10Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber10Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber10Block0Chunk0ParentMapAudit,
    tttLargeFiber10Block0Chunk0ParentMap_0_ok,
    tttLargeFiber10Block0Chunk0ParentMap_1_ok,
    tttLargeFiber10Block0Chunk0ParentMap_2_ok,
    tttLargeFiber10Block0Chunk0ParentMap_3_ok,
    tttLargeFiber10Block0Chunk0ParentMap_4_ok,
    tttLargeFiber10Block0Chunk0ParentMap_5_ok,
    tttLargeFiber10Block0Chunk0ParentMap_6_ok,
    tttLargeFiber10Block0Chunk0ParentMap_7_ok,
    tttLargeFiber10Block0Chunk0ParentMap_8_ok,
    tttLargeFiber10Block0Chunk0ParentMap_9_ok,
    tttLargeFiber10Block0Chunk0ParentMap_10_ok,
    tttLargeFiber10Block0Chunk0ParentMap_11_ok,
    tttLargeFiber10Block0Chunk0ParentMap_12_ok,
    tttLargeFiber10Block0Chunk0ParentMap_13_ok,
    tttLargeFiber10Block0Chunk0ParentMap_14_ok,
    tttLargeFiber10Block0Chunk0ParentMap_15_ok]

def tttLargeFiber10Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber10Block0Chunk0ParentPathCheck 0
    && tttLargeFiber10Block0Chunk0ParentPathCheck 1
    && tttLargeFiber10Block0Chunk0ParentPathCheck 2
    && tttLargeFiber10Block0Chunk0ParentPathCheck 3
    && tttLargeFiber10Block0Chunk0ParentPathCheck 4
    && tttLargeFiber10Block0Chunk0ParentPathCheck 5
    && tttLargeFiber10Block0Chunk0ParentPathCheck 6
    && tttLargeFiber10Block0Chunk0ParentPathCheck 7
    && tttLargeFiber10Block0Chunk0ParentPathCheck 8
    && tttLargeFiber10Block0Chunk0ParentPathCheck 9
    && tttLargeFiber10Block0Chunk0ParentPathCheck 10
    && tttLargeFiber10Block0Chunk0ParentPathCheck 11
    && tttLargeFiber10Block0Chunk0ParentPathCheck 12
    && tttLargeFiber10Block0Chunk0ParentPathCheck 13
    && tttLargeFiber10Block0Chunk0ParentPathCheck 14
    && tttLargeFiber10Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber10Block0Chunk0ParentsAudit_ok :
    tttLargeFiber10Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber10Block0Chunk0ParentsAudit,
    tttLargeFiber10Block0Chunk0ParentPath_0_ok,
    tttLargeFiber10Block0Chunk0ParentPath_1_ok,
    tttLargeFiber10Block0Chunk0ParentPath_2_ok,
    tttLargeFiber10Block0Chunk0ParentPath_3_ok,
    tttLargeFiber10Block0Chunk0ParentPath_4_ok,
    tttLargeFiber10Block0Chunk0ParentPath_5_ok,
    tttLargeFiber10Block0Chunk0ParentPath_6_ok,
    tttLargeFiber10Block0Chunk0ParentPath_7_ok,
    tttLargeFiber10Block0Chunk0ParentPath_8_ok,
    tttLargeFiber10Block0Chunk0ParentPath_9_ok,
    tttLargeFiber10Block0Chunk0ParentPath_10_ok,
    tttLargeFiber10Block0Chunk0ParentPath_11_ok,
    tttLargeFiber10Block0Chunk0ParentPath_12_ok,
    tttLargeFiber10Block0Chunk0ParentPath_13_ok,
    tttLargeFiber10Block0Chunk0ParentPath_14_ok,
    tttLargeFiber10Block0Chunk0ParentPath_15_ok]

def tttLargeFiber10Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block0Chunk0SourcesCheck &&
    tttLargeFiber10Block0Chunk0RowsAudit &&
    tttLargeFiber10Block0Chunk0ParentMapAudit &&
    tttLargeFiber10Block0Chunk0ParentsAudit

theorem tttLargeFiber10Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber10Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block0Chunk0SourcesCheck_ok,
    tttLargeFiber10Block0Chunk0RowsAudit_ok,
    tttLargeFiber10Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber10Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
