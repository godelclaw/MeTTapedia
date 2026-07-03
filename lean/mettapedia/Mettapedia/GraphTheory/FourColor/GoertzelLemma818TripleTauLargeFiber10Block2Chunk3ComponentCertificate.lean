import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 2 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block2Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block2Chunk3Sources : List Nat :=
  [   2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631,
   2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]

def tttLargeFiber10Row176 : TripleComponentParentRow :=
  tripleRow 2624 2496 74 34 0 72 102 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row177 : TripleComponentParentRow :=
  tripleRow 2625 2497 74 34 1 72 102 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row178 : TripleComponentParentRow :=
  tripleRow 2626 2498 74 34 2 72 102 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row179 : TripleComponentParentRow :=
  tripleRow 2627 2499 74 34 3 72 102 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row180 : TripleComponentParentRow :=
  tripleRow 2628 2624 74 34 48 74 34 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row181 : TripleComponentParentRow :=
  tripleRow 2629 2625 74 34 49 74 34 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row182 : TripleComponentParentRow :=
  tripleRow 2630 2502 74 34 50 72 102 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row183 : TripleComponentParentRow :=
  tripleRow 2631 2503 74 34 51 72 102 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row184 : TripleComponentParentRow :=
  tripleRow 2632 2504 74 35 8 72 103 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row185 : TripleComponentParentRow :=
  tripleRow 2633 2505 74 35 9 72 103 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row186 : TripleComponentParentRow :=
  tripleRow 2634 2506 74 35 10 72 103 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row187 : TripleComponentParentRow :=
  tripleRow 2635 2507 74 35 11 72 103 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row188 : TripleComponentParentRow :=
  tripleRow 2636 2632 74 35 56 74 35 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row189 : TripleComponentParentRow :=
  tripleRow 2637 2633 74 35 57 74 35 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row190 : TripleComponentParentRow :=
  tripleRow 2638 2510 74 35 58 72 103 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row191 : TripleComponentParentRow :=
  tripleRow 2639 2511 74 35 59 72 103 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Block2Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row176
  , tttLargeFiber10Row177
  , tttLargeFiber10Row178
  , tttLargeFiber10Row179
  , tttLargeFiber10Row180
  , tttLargeFiber10Row181
  , tttLargeFiber10Row182
  , tttLargeFiber10Row183
  , tttLargeFiber10Row184
  , tttLargeFiber10Row185
  , tttLargeFiber10Row186
  , tttLargeFiber10Row187
  , tttLargeFiber10Row188
  , tttLargeFiber10Row189
  , tttLargeFiber10Row190
  , tttLargeFiber10Row191
  ]

def tttLargeFiber10Block2Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block2Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block2Chunk3ExpectedContains row.source &&
    tttLargeFiber10Block2Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block2Chunk3SourcesCheck : Bool :=
  (tttLargeFiber10Block2Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber10Block2Chunk3Sources

theorem tttLargeFiber10Block2Chunk3SourcesCheck_ok :
    tttLargeFiber10Block2Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber10Block2Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block2Chunk3RowValid
    (listGetD tttLargeFiber10Block2Chunk3Rows i default)

def tttLargeFiber10Block2Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block2Chunk3Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block2Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block2Chunk3Sources 0 0 == 2624
      && tttLargeFiber10ParentOf 2624 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block2Chunk3Sources 1 0 == 2625
      && tttLargeFiber10ParentOf 2625 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block2Chunk3Sources 2 0 == 2626
      && tttLargeFiber10ParentOf 2626 == 2498
      && tttLargeFiber10ParentOf 2498 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block2Chunk3Sources 3 0 == 2627
      && tttLargeFiber10ParentOf 2627 == 2499
      && tttLargeFiber10ParentOf 2499 == 2459
      && tttLargeFiber10ParentOf 2459 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block2Chunk3Sources 4 0 == 2628
      && tttLargeFiber10ParentOf 2628 == 2624
      && tttLargeFiber10ParentOf 2624 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block2Chunk3Sources 5 0 == 2629
      && tttLargeFiber10ParentOf 2629 == 2625
      && tttLargeFiber10ParentOf 2625 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block2Chunk3Sources 6 0 == 2630
      && tttLargeFiber10ParentOf 2630 == 2502
      && tttLargeFiber10ParentOf 2502 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block2Chunk3Sources 7 0 == 2631
      && tttLargeFiber10ParentOf 2631 == 2503
      && tttLargeFiber10ParentOf 2503 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block2Chunk3Sources 8 0 == 2632
      && tttLargeFiber10ParentOf 2632 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block2Chunk3Sources 9 0 == 2633
      && tttLargeFiber10ParentOf 2633 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block2Chunk3Sources 10 0 == 2634
      && tttLargeFiber10ParentOf 2634 == 2506
      && tttLargeFiber10ParentOf 2506 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block2Chunk3Sources 11 0 == 2635
      && tttLargeFiber10ParentOf 2635 == 2507
      && tttLargeFiber10ParentOf 2507 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block2Chunk3Sources 12 0 == 2636
      && tttLargeFiber10ParentOf 2636 == 2632
      && tttLargeFiber10ParentOf 2632 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block2Chunk3Sources 13 0 == 2637
      && tttLargeFiber10ParentOf 2637 == 2633
      && tttLargeFiber10ParentOf 2633 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block2Chunk3Sources 14 0 == 2638
      && tttLargeFiber10ParentOf 2638 == 2510
      && tttLargeFiber10ParentOf 2510 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block2Chunk3Sources 15 0 == 2639
      && tttLargeFiber10ParentOf 2639 == 2511
      && tttLargeFiber10ParentOf 2511 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block2Chunk3Row_0_ok :
    tttLargeFiber10Block2Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_1_ok :
    tttLargeFiber10Block2Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_2_ok :
    tttLargeFiber10Block2Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_3_ok :
    tttLargeFiber10Block2Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_4_ok :
    tttLargeFiber10Block2Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_5_ok :
    tttLargeFiber10Block2Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_6_ok :
    tttLargeFiber10Block2Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_7_ok :
    tttLargeFiber10Block2Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_8_ok :
    tttLargeFiber10Block2Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_9_ok :
    tttLargeFiber10Block2Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_10_ok :
    tttLargeFiber10Block2Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_11_ok :
    tttLargeFiber10Block2Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_12_ok :
    tttLargeFiber10Block2Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_13_ok :
    tttLargeFiber10Block2Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_14_ok :
    tttLargeFiber10Block2Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3Row_15_ok :
    tttLargeFiber10Block2Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_0_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_1_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_2_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_3_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_4_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_5_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_6_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_7_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_8_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_9_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_10_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_11_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_12_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_13_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_14_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentMap_15_ok :
    tttLargeFiber10Block2Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_0_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_1_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_2_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_3_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_4_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_5_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_6_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_7_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_8_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_9_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_10_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_11_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_12_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_13_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_14_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block2Chunk3ParentPath_15_ok :
    tttLargeFiber10Block2Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block2Chunk3RowsAudit : Bool :=
  tttLargeFiber10Block2Chunk3RowCheck 0
    && tttLargeFiber10Block2Chunk3RowCheck 1
    && tttLargeFiber10Block2Chunk3RowCheck 2
    && tttLargeFiber10Block2Chunk3RowCheck 3
    && tttLargeFiber10Block2Chunk3RowCheck 4
    && tttLargeFiber10Block2Chunk3RowCheck 5
    && tttLargeFiber10Block2Chunk3RowCheck 6
    && tttLargeFiber10Block2Chunk3RowCheck 7
    && tttLargeFiber10Block2Chunk3RowCheck 8
    && tttLargeFiber10Block2Chunk3RowCheck 9
    && tttLargeFiber10Block2Chunk3RowCheck 10
    && tttLargeFiber10Block2Chunk3RowCheck 11
    && tttLargeFiber10Block2Chunk3RowCheck 12
    && tttLargeFiber10Block2Chunk3RowCheck 13
    && tttLargeFiber10Block2Chunk3RowCheck 14
    && tttLargeFiber10Block2Chunk3RowCheck 15

theorem tttLargeFiber10Block2Chunk3RowsAudit_ok :
    tttLargeFiber10Block2Chunk3RowsAudit = true := by
  simp [tttLargeFiber10Block2Chunk3RowsAudit,
    tttLargeFiber10Block2Chunk3Row_0_ok,
    tttLargeFiber10Block2Chunk3Row_1_ok,
    tttLargeFiber10Block2Chunk3Row_2_ok,
    tttLargeFiber10Block2Chunk3Row_3_ok,
    tttLargeFiber10Block2Chunk3Row_4_ok,
    tttLargeFiber10Block2Chunk3Row_5_ok,
    tttLargeFiber10Block2Chunk3Row_6_ok,
    tttLargeFiber10Block2Chunk3Row_7_ok,
    tttLargeFiber10Block2Chunk3Row_8_ok,
    tttLargeFiber10Block2Chunk3Row_9_ok,
    tttLargeFiber10Block2Chunk3Row_10_ok,
    tttLargeFiber10Block2Chunk3Row_11_ok,
    tttLargeFiber10Block2Chunk3Row_12_ok,
    tttLargeFiber10Block2Chunk3Row_13_ok,
    tttLargeFiber10Block2Chunk3Row_14_ok,
    tttLargeFiber10Block2Chunk3Row_15_ok]

def tttLargeFiber10Block2Chunk3ParentMapAudit : Bool :=
  tttLargeFiber10Block2Chunk3ParentMapCheck 0
    && tttLargeFiber10Block2Chunk3ParentMapCheck 1
    && tttLargeFiber10Block2Chunk3ParentMapCheck 2
    && tttLargeFiber10Block2Chunk3ParentMapCheck 3
    && tttLargeFiber10Block2Chunk3ParentMapCheck 4
    && tttLargeFiber10Block2Chunk3ParentMapCheck 5
    && tttLargeFiber10Block2Chunk3ParentMapCheck 6
    && tttLargeFiber10Block2Chunk3ParentMapCheck 7
    && tttLargeFiber10Block2Chunk3ParentMapCheck 8
    && tttLargeFiber10Block2Chunk3ParentMapCheck 9
    && tttLargeFiber10Block2Chunk3ParentMapCheck 10
    && tttLargeFiber10Block2Chunk3ParentMapCheck 11
    && tttLargeFiber10Block2Chunk3ParentMapCheck 12
    && tttLargeFiber10Block2Chunk3ParentMapCheck 13
    && tttLargeFiber10Block2Chunk3ParentMapCheck 14
    && tttLargeFiber10Block2Chunk3ParentMapCheck 15

theorem tttLargeFiber10Block2Chunk3ParentMapAudit_ok :
    tttLargeFiber10Block2Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber10Block2Chunk3ParentMapAudit,
    tttLargeFiber10Block2Chunk3ParentMap_0_ok,
    tttLargeFiber10Block2Chunk3ParentMap_1_ok,
    tttLargeFiber10Block2Chunk3ParentMap_2_ok,
    tttLargeFiber10Block2Chunk3ParentMap_3_ok,
    tttLargeFiber10Block2Chunk3ParentMap_4_ok,
    tttLargeFiber10Block2Chunk3ParentMap_5_ok,
    tttLargeFiber10Block2Chunk3ParentMap_6_ok,
    tttLargeFiber10Block2Chunk3ParentMap_7_ok,
    tttLargeFiber10Block2Chunk3ParentMap_8_ok,
    tttLargeFiber10Block2Chunk3ParentMap_9_ok,
    tttLargeFiber10Block2Chunk3ParentMap_10_ok,
    tttLargeFiber10Block2Chunk3ParentMap_11_ok,
    tttLargeFiber10Block2Chunk3ParentMap_12_ok,
    tttLargeFiber10Block2Chunk3ParentMap_13_ok,
    tttLargeFiber10Block2Chunk3ParentMap_14_ok,
    tttLargeFiber10Block2Chunk3ParentMap_15_ok]

def tttLargeFiber10Block2Chunk3ParentsAudit : Bool :=
  tttLargeFiber10Block2Chunk3ParentPathCheck 0
    && tttLargeFiber10Block2Chunk3ParentPathCheck 1
    && tttLargeFiber10Block2Chunk3ParentPathCheck 2
    && tttLargeFiber10Block2Chunk3ParentPathCheck 3
    && tttLargeFiber10Block2Chunk3ParentPathCheck 4
    && tttLargeFiber10Block2Chunk3ParentPathCheck 5
    && tttLargeFiber10Block2Chunk3ParentPathCheck 6
    && tttLargeFiber10Block2Chunk3ParentPathCheck 7
    && tttLargeFiber10Block2Chunk3ParentPathCheck 8
    && tttLargeFiber10Block2Chunk3ParentPathCheck 9
    && tttLargeFiber10Block2Chunk3ParentPathCheck 10
    && tttLargeFiber10Block2Chunk3ParentPathCheck 11
    && tttLargeFiber10Block2Chunk3ParentPathCheck 12
    && tttLargeFiber10Block2Chunk3ParentPathCheck 13
    && tttLargeFiber10Block2Chunk3ParentPathCheck 14
    && tttLargeFiber10Block2Chunk3ParentPathCheck 15

theorem tttLargeFiber10Block2Chunk3ParentsAudit_ok :
    tttLargeFiber10Block2Chunk3ParentsAudit = true := by
  simp [tttLargeFiber10Block2Chunk3ParentsAudit,
    tttLargeFiber10Block2Chunk3ParentPath_0_ok,
    tttLargeFiber10Block2Chunk3ParentPath_1_ok,
    tttLargeFiber10Block2Chunk3ParentPath_2_ok,
    tttLargeFiber10Block2Chunk3ParentPath_3_ok,
    tttLargeFiber10Block2Chunk3ParentPath_4_ok,
    tttLargeFiber10Block2Chunk3ParentPath_5_ok,
    tttLargeFiber10Block2Chunk3ParentPath_6_ok,
    tttLargeFiber10Block2Chunk3ParentPath_7_ok,
    tttLargeFiber10Block2Chunk3ParentPath_8_ok,
    tttLargeFiber10Block2Chunk3ParentPath_9_ok,
    tttLargeFiber10Block2Chunk3ParentPath_10_ok,
    tttLargeFiber10Block2Chunk3ParentPath_11_ok,
    tttLargeFiber10Block2Chunk3ParentPath_12_ok,
    tttLargeFiber10Block2Chunk3ParentPath_13_ok,
    tttLargeFiber10Block2Chunk3ParentPath_14_ok,
    tttLargeFiber10Block2Chunk3ParentPath_15_ok]

def tttLargeFiber10Block2Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block2Chunk3SourcesCheck &&
    tttLargeFiber10Block2Chunk3RowsAudit &&
    tttLargeFiber10Block2Chunk3ParentMapAudit &&
    tttLargeFiber10Block2Chunk3ParentsAudit

theorem tttLargeFiber10Block2Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber10Block2Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block2Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block2Chunk3SourcesCheck_ok,
    tttLargeFiber10Block2Chunk3RowsAudit_ok,
    tttLargeFiber10Block2Chunk3ParentMapAudit_ok,
    tttLargeFiber10Block2Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block2Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
