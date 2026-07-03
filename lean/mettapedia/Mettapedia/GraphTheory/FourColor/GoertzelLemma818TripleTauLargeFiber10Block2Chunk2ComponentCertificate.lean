import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 2 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block2Chunk2Sources : List Nat :=
  [   2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615,
   2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]

def tttLargeFiber10Row160 : TripleComponentParentRow :=
  tripleRow 2608 2576 74 32 148 74 16 80
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

def tttLargeFiber10Row161 : TripleComponentParentRow :=
  tripleRow 2609 2577 74 32 149 74 16 81
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

def tttLargeFiber10Row162 : TripleComponentParentRow :=
  tripleRow 2610 2578 74 32 150 74 16 82
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

def tttLargeFiber10Row163 : TripleComponentParentRow :=
  tripleRow 2611 2608 74 32 151 74 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row164 : TripleComponentParentRow :=
  tripleRow 2612 2608 74 32 164 74 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row165 : TripleComponentParentRow :=
  tripleRow 2613 2609 74 32 165 74 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row166 : TripleComponentParentRow :=
  tripleRow 2614 2582 74 32 166 74 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row167 : TripleComponentParentRow :=
  tripleRow 2615 2583 74 32 167 74 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row168 : TripleComponentParentRow :=
  tripleRow 2616 2584 74 33 156 74 17 88
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

def tttLargeFiber10Row169 : TripleComponentParentRow :=
  tripleRow 2617 2585 74 33 157 74 17 89
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

def tttLargeFiber10Row170 : TripleComponentParentRow :=
  tripleRow 2618 2586 74 33 158 74 17 90
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

def tttLargeFiber10Row171 : TripleComponentParentRow :=
  tripleRow 2619 2616 74 33 159 74 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row172 : TripleComponentParentRow :=
  tripleRow 2620 2616 74 33 172 74 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row173 : TripleComponentParentRow :=
  tripleRow 2621 2617 74 33 173 74 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row174 : TripleComponentParentRow :=
  tripleRow 2622 2590 74 33 174 74 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Row175 : TripleComponentParentRow :=
  tripleRow 2623 2591 74 33 175 74 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber10Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row160
  , tttLargeFiber10Row161
  , tttLargeFiber10Row162
  , tttLargeFiber10Row163
  , tttLargeFiber10Row164
  , tttLargeFiber10Row165
  , tttLargeFiber10Row166
  , tttLargeFiber10Row167
  , tttLargeFiber10Row168
  , tttLargeFiber10Row169
  , tttLargeFiber10Row170
  , tttLargeFiber10Row171
  , tttLargeFiber10Row172
  , tttLargeFiber10Row173
  , tttLargeFiber10Row174
  , tttLargeFiber10Row175
  ]

def tttLargeFiber10Block2Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block2Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block2Chunk2ExpectedContains row.source &&
    tttLargeFiber10Block2Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber10Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber10Block2Chunk2Sources

theorem tttLargeFiber10Block2Chunk2SourcesCheck_ok :
    tttLargeFiber10Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber10Block2Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block2Chunk2RowValid
    (listGetD tttLargeFiber10Block2Chunk2Rows i default)

def tttLargeFiber10Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block2Chunk2Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block2Chunk2Sources 0 0 == 2608
      && tttLargeFiber10ParentOf 2608 == 2576
      && tttLargeFiber10ParentOf 2576 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block2Chunk2Sources 1 0 == 2609
      && tttLargeFiber10ParentOf 2609 == 2577
      && tttLargeFiber10ParentOf 2577 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block2Chunk2Sources 2 0 == 2610
      && tttLargeFiber10ParentOf 2610 == 2578
      && tttLargeFiber10ParentOf 2578 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block2Chunk2Sources 3 0 == 2611
      && tttLargeFiber10ParentOf 2611 == 2608
      && tttLargeFiber10ParentOf 2608 == 2576
      && tttLargeFiber10ParentOf 2576 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block2Chunk2Sources 4 0 == 2612
      && tttLargeFiber10ParentOf 2612 == 2608
      && tttLargeFiber10ParentOf 2608 == 2576
      && tttLargeFiber10ParentOf 2576 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block2Chunk2Sources 5 0 == 2613
      && tttLargeFiber10ParentOf 2613 == 2609
      && tttLargeFiber10ParentOf 2609 == 2577
      && tttLargeFiber10ParentOf 2577 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block2Chunk2Sources 6 0 == 2614
      && tttLargeFiber10ParentOf 2614 == 2582
      && tttLargeFiber10ParentOf 2582 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block2Chunk2Sources 7 0 == 2615
      && tttLargeFiber10ParentOf 2615 == 2583
      && tttLargeFiber10ParentOf 2583 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block2Chunk2Sources 8 0 == 2616
      && tttLargeFiber10ParentOf 2616 == 2584
      && tttLargeFiber10ParentOf 2584 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block2Chunk2Sources 9 0 == 2617
      && tttLargeFiber10ParentOf 2617 == 2585
      && tttLargeFiber10ParentOf 2585 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block2Chunk2Sources 10 0 == 2618
      && tttLargeFiber10ParentOf 2618 == 2586
      && tttLargeFiber10ParentOf 2586 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block2Chunk2Sources 11 0 == 2619
      && tttLargeFiber10ParentOf 2619 == 2616
      && tttLargeFiber10ParentOf 2616 == 2584
      && tttLargeFiber10ParentOf 2584 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block2Chunk2Sources 12 0 == 2620
      && tttLargeFiber10ParentOf 2620 == 2616
      && tttLargeFiber10ParentOf 2616 == 2584
      && tttLargeFiber10ParentOf 2584 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block2Chunk2Sources 13 0 == 2621
      && tttLargeFiber10ParentOf 2621 == 2617
      && tttLargeFiber10ParentOf 2617 == 2585
      && tttLargeFiber10ParentOf 2585 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block2Chunk2Sources 14 0 == 2622
      && tttLargeFiber10ParentOf 2622 == 2590
      && tttLargeFiber10ParentOf 2590 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block2Chunk2Sources 15 0 == 2623
      && tttLargeFiber10ParentOf 2623 == 2591
      && tttLargeFiber10ParentOf 2591 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block2Chunk2Row_0_ok :
    tttLargeFiber10Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_1_ok :
    tttLargeFiber10Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_2_ok :
    tttLargeFiber10Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_3_ok :
    tttLargeFiber10Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_4_ok :
    tttLargeFiber10Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_5_ok :
    tttLargeFiber10Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_6_ok :
    tttLargeFiber10Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_7_ok :
    tttLargeFiber10Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_8_ok :
    tttLargeFiber10Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_9_ok :
    tttLargeFiber10Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_10_ok :
    tttLargeFiber10Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_11_ok :
    tttLargeFiber10Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_12_ok :
    tttLargeFiber10Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_13_ok :
    tttLargeFiber10Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_14_ok :
    tttLargeFiber10Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2Row_15_ok :
    tttLargeFiber10Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_0_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_1_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_2_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_3_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_4_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_5_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_6_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_7_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_8_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_9_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_10_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_11_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_12_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_13_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_14_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentMap_15_ok :
    tttLargeFiber10Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_0_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_1_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_2_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_3_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_4_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_5_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_6_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_7_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_8_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_9_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_10_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_11_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_12_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_13_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_14_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block2Chunk2ParentPath_15_ok :
    tttLargeFiber10Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber10Block2Chunk2RowCheck 0
    && tttLargeFiber10Block2Chunk2RowCheck 1
    && tttLargeFiber10Block2Chunk2RowCheck 2
    && tttLargeFiber10Block2Chunk2RowCheck 3
    && tttLargeFiber10Block2Chunk2RowCheck 4
    && tttLargeFiber10Block2Chunk2RowCheck 5
    && tttLargeFiber10Block2Chunk2RowCheck 6
    && tttLargeFiber10Block2Chunk2RowCheck 7
    && tttLargeFiber10Block2Chunk2RowCheck 8
    && tttLargeFiber10Block2Chunk2RowCheck 9
    && tttLargeFiber10Block2Chunk2RowCheck 10
    && tttLargeFiber10Block2Chunk2RowCheck 11
    && tttLargeFiber10Block2Chunk2RowCheck 12
    && tttLargeFiber10Block2Chunk2RowCheck 13
    && tttLargeFiber10Block2Chunk2RowCheck 14
    && tttLargeFiber10Block2Chunk2RowCheck 15

theorem tttLargeFiber10Block2Chunk2RowsAudit_ok :
    tttLargeFiber10Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber10Block2Chunk2RowsAudit,
    tttLargeFiber10Block2Chunk2Row_0_ok,
    tttLargeFiber10Block2Chunk2Row_1_ok,
    tttLargeFiber10Block2Chunk2Row_2_ok,
    tttLargeFiber10Block2Chunk2Row_3_ok,
    tttLargeFiber10Block2Chunk2Row_4_ok,
    tttLargeFiber10Block2Chunk2Row_5_ok,
    tttLargeFiber10Block2Chunk2Row_6_ok,
    tttLargeFiber10Block2Chunk2Row_7_ok,
    tttLargeFiber10Block2Chunk2Row_8_ok,
    tttLargeFiber10Block2Chunk2Row_9_ok,
    tttLargeFiber10Block2Chunk2Row_10_ok,
    tttLargeFiber10Block2Chunk2Row_11_ok,
    tttLargeFiber10Block2Chunk2Row_12_ok,
    tttLargeFiber10Block2Chunk2Row_13_ok,
    tttLargeFiber10Block2Chunk2Row_14_ok,
    tttLargeFiber10Block2Chunk2Row_15_ok]

def tttLargeFiber10Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber10Block2Chunk2ParentMapCheck 0
    && tttLargeFiber10Block2Chunk2ParentMapCheck 1
    && tttLargeFiber10Block2Chunk2ParentMapCheck 2
    && tttLargeFiber10Block2Chunk2ParentMapCheck 3
    && tttLargeFiber10Block2Chunk2ParentMapCheck 4
    && tttLargeFiber10Block2Chunk2ParentMapCheck 5
    && tttLargeFiber10Block2Chunk2ParentMapCheck 6
    && tttLargeFiber10Block2Chunk2ParentMapCheck 7
    && tttLargeFiber10Block2Chunk2ParentMapCheck 8
    && tttLargeFiber10Block2Chunk2ParentMapCheck 9
    && tttLargeFiber10Block2Chunk2ParentMapCheck 10
    && tttLargeFiber10Block2Chunk2ParentMapCheck 11
    && tttLargeFiber10Block2Chunk2ParentMapCheck 12
    && tttLargeFiber10Block2Chunk2ParentMapCheck 13
    && tttLargeFiber10Block2Chunk2ParentMapCheck 14
    && tttLargeFiber10Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber10Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber10Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber10Block2Chunk2ParentMapAudit,
    tttLargeFiber10Block2Chunk2ParentMap_0_ok,
    tttLargeFiber10Block2Chunk2ParentMap_1_ok,
    tttLargeFiber10Block2Chunk2ParentMap_2_ok,
    tttLargeFiber10Block2Chunk2ParentMap_3_ok,
    tttLargeFiber10Block2Chunk2ParentMap_4_ok,
    tttLargeFiber10Block2Chunk2ParentMap_5_ok,
    tttLargeFiber10Block2Chunk2ParentMap_6_ok,
    tttLargeFiber10Block2Chunk2ParentMap_7_ok,
    tttLargeFiber10Block2Chunk2ParentMap_8_ok,
    tttLargeFiber10Block2Chunk2ParentMap_9_ok,
    tttLargeFiber10Block2Chunk2ParentMap_10_ok,
    tttLargeFiber10Block2Chunk2ParentMap_11_ok,
    tttLargeFiber10Block2Chunk2ParentMap_12_ok,
    tttLargeFiber10Block2Chunk2ParentMap_13_ok,
    tttLargeFiber10Block2Chunk2ParentMap_14_ok,
    tttLargeFiber10Block2Chunk2ParentMap_15_ok]

def tttLargeFiber10Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber10Block2Chunk2ParentPathCheck 0
    && tttLargeFiber10Block2Chunk2ParentPathCheck 1
    && tttLargeFiber10Block2Chunk2ParentPathCheck 2
    && tttLargeFiber10Block2Chunk2ParentPathCheck 3
    && tttLargeFiber10Block2Chunk2ParentPathCheck 4
    && tttLargeFiber10Block2Chunk2ParentPathCheck 5
    && tttLargeFiber10Block2Chunk2ParentPathCheck 6
    && tttLargeFiber10Block2Chunk2ParentPathCheck 7
    && tttLargeFiber10Block2Chunk2ParentPathCheck 8
    && tttLargeFiber10Block2Chunk2ParentPathCheck 9
    && tttLargeFiber10Block2Chunk2ParentPathCheck 10
    && tttLargeFiber10Block2Chunk2ParentPathCheck 11
    && tttLargeFiber10Block2Chunk2ParentPathCheck 12
    && tttLargeFiber10Block2Chunk2ParentPathCheck 13
    && tttLargeFiber10Block2Chunk2ParentPathCheck 14
    && tttLargeFiber10Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber10Block2Chunk2ParentsAudit_ok :
    tttLargeFiber10Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber10Block2Chunk2ParentsAudit,
    tttLargeFiber10Block2Chunk2ParentPath_0_ok,
    tttLargeFiber10Block2Chunk2ParentPath_1_ok,
    tttLargeFiber10Block2Chunk2ParentPath_2_ok,
    tttLargeFiber10Block2Chunk2ParentPath_3_ok,
    tttLargeFiber10Block2Chunk2ParentPath_4_ok,
    tttLargeFiber10Block2Chunk2ParentPath_5_ok,
    tttLargeFiber10Block2Chunk2ParentPath_6_ok,
    tttLargeFiber10Block2Chunk2ParentPath_7_ok,
    tttLargeFiber10Block2Chunk2ParentPath_8_ok,
    tttLargeFiber10Block2Chunk2ParentPath_9_ok,
    tttLargeFiber10Block2Chunk2ParentPath_10_ok,
    tttLargeFiber10Block2Chunk2ParentPath_11_ok,
    tttLargeFiber10Block2Chunk2ParentPath_12_ok,
    tttLargeFiber10Block2Chunk2ParentPath_13_ok,
    tttLargeFiber10Block2Chunk2ParentPath_14_ok,
    tttLargeFiber10Block2Chunk2ParentPath_15_ok]

def tttLargeFiber10Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block2Chunk2SourcesCheck &&
    tttLargeFiber10Block2Chunk2RowsAudit &&
    tttLargeFiber10Block2Chunk2ParentMapAudit &&
    tttLargeFiber10Block2Chunk2ParentsAudit

theorem tttLargeFiber10Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber10Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block2Chunk2SourcesCheck_ok,
    tttLargeFiber10Block2Chunk2RowsAudit_ok,
    tttLargeFiber10Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber10Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
