import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block0Chunk0Sources : List Nat :=
  [   544, 545, 546, 547, 548, 549, 550, 551,
   552, 553, 554, 555, 556, 557, 558, 559]

def tttLargeFiber60Row0 : TripleComponentParentRow :=
  tripleRow 544 544 16 80 80 16 80 80
    default
    []

def tttLargeFiber60Row1 : TripleComponentParentRow :=
  tripleRow 545 544 16 80 81 16 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row2 : TripleComponentParentRow :=
  tripleRow 546 544 16 80 82 16 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row3 : TripleComponentParentRow :=
  tripleRow 547 545 16 80 83 16 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row4 : TripleComponentParentRow :=
  tripleRow 548 546 16 80 100 16 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row5 : TripleComponentParentRow :=
  tripleRow 549 551 16 80 101 16 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row6 : TripleComponentParentRow :=
  tripleRow 550 545 16 80 102 16 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row7 : TripleComponentParentRow :=
  tripleRow 551 544 16 80 103 16 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row8 : TripleComponentParentRow :=
  tripleRow 552 544 16 81 88 16 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row9 : TripleComponentParentRow :=
  tripleRow 553 545 16 81 89 16 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row10 : TripleComponentParentRow :=
  tripleRow 554 546 16 81 90 16 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row11 : TripleComponentParentRow :=
  tripleRow 555 547 16 81 91 16 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row12 : TripleComponentParentRow :=
  tripleRow 556 548 16 81 108 16 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row13 : TripleComponentParentRow :=
  tripleRow 557 549 16 81 109 16 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row14 : TripleComponentParentRow :=
  tripleRow 558 550 16 81 110 16 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row15 : TripleComponentParentRow :=
  tripleRow 559 551 16 81 111 16 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row0
  , tttLargeFiber60Row1
  , tttLargeFiber60Row2
  , tttLargeFiber60Row3
  , tttLargeFiber60Row4
  , tttLargeFiber60Row5
  , tttLargeFiber60Row6
  , tttLargeFiber60Row7
  , tttLargeFiber60Row8
  , tttLargeFiber60Row9
  , tttLargeFiber60Row10
  , tttLargeFiber60Row11
  , tttLargeFiber60Row12
  , tttLargeFiber60Row13
  , tttLargeFiber60Row14
  , tttLargeFiber60Row15
  ]

def tttLargeFiber60Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber60Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber60Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber60Block0Chunk0Sources

theorem tttLargeFiber60Block0Chunk0SourcesCheck_ok :
    tttLargeFiber60Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber60Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block0Chunk0RowValid
    (listGetD tttLargeFiber60Block0Chunk0Rows i default)

def tttLargeFiber60Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block0Chunk0Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block0Chunk0Sources 0 0 == 544
      && 544 == tttLargeFiber60Root
      && decide (0 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block0Chunk0Sources 1 0 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (1 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block0Chunk0Sources 2 0 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (1 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block0Chunk0Sources 3 0 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block0Chunk0Sources 4 0 == 548
      && tttLargeFiber60ParentOf 548 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block0Chunk0Sources 5 0 == 549
      && tttLargeFiber60ParentOf 549 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block0Chunk0Sources 6 0 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block0Chunk0Sources 7 0 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (1 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block0Chunk0Sources 8 0 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (1 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block0Chunk0Sources 9 0 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block0Chunk0Sources 10 0 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block0Chunk0Sources 11 0 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block0Chunk0Sources 12 0 == 556
      && tttLargeFiber60ParentOf 556 == 548
      && tttLargeFiber60ParentOf 548 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block0Chunk0Sources 13 0 == 557
      && tttLargeFiber60ParentOf 557 == 549
      && tttLargeFiber60ParentOf 549 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block0Chunk0Sources 14 0 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block0Chunk0Sources 15 0 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block0Chunk0Row_0_ok :
    tttLargeFiber60Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_1_ok :
    tttLargeFiber60Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_2_ok :
    tttLargeFiber60Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_3_ok :
    tttLargeFiber60Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_4_ok :
    tttLargeFiber60Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_5_ok :
    tttLargeFiber60Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_6_ok :
    tttLargeFiber60Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_7_ok :
    tttLargeFiber60Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_8_ok :
    tttLargeFiber60Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_9_ok :
    tttLargeFiber60Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_10_ok :
    tttLargeFiber60Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_11_ok :
    tttLargeFiber60Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_12_ok :
    tttLargeFiber60Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_13_ok :
    tttLargeFiber60Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_14_ok :
    tttLargeFiber60Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0Row_15_ok :
    tttLargeFiber60Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_0_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_1_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_2_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_3_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_4_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_5_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_6_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_7_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_8_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_9_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_10_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_11_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_12_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_13_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_14_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentMap_15_ok :
    tttLargeFiber60Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_0_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_1_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_2_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_3_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_4_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_5_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_6_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_7_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_8_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_9_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_10_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_11_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_12_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_13_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_14_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block0Chunk0ParentPath_15_ok :
    tttLargeFiber60Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber60Block0Chunk0RowCheck 0
    && tttLargeFiber60Block0Chunk0RowCheck 1
    && tttLargeFiber60Block0Chunk0RowCheck 2
    && tttLargeFiber60Block0Chunk0RowCheck 3
    && tttLargeFiber60Block0Chunk0RowCheck 4
    && tttLargeFiber60Block0Chunk0RowCheck 5
    && tttLargeFiber60Block0Chunk0RowCheck 6
    && tttLargeFiber60Block0Chunk0RowCheck 7
    && tttLargeFiber60Block0Chunk0RowCheck 8
    && tttLargeFiber60Block0Chunk0RowCheck 9
    && tttLargeFiber60Block0Chunk0RowCheck 10
    && tttLargeFiber60Block0Chunk0RowCheck 11
    && tttLargeFiber60Block0Chunk0RowCheck 12
    && tttLargeFiber60Block0Chunk0RowCheck 13
    && tttLargeFiber60Block0Chunk0RowCheck 14
    && tttLargeFiber60Block0Chunk0RowCheck 15

theorem tttLargeFiber60Block0Chunk0RowsAudit_ok :
    tttLargeFiber60Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber60Block0Chunk0RowsAudit,
    tttLargeFiber60Block0Chunk0Row_0_ok,
    tttLargeFiber60Block0Chunk0Row_1_ok,
    tttLargeFiber60Block0Chunk0Row_2_ok,
    tttLargeFiber60Block0Chunk0Row_3_ok,
    tttLargeFiber60Block0Chunk0Row_4_ok,
    tttLargeFiber60Block0Chunk0Row_5_ok,
    tttLargeFiber60Block0Chunk0Row_6_ok,
    tttLargeFiber60Block0Chunk0Row_7_ok,
    tttLargeFiber60Block0Chunk0Row_8_ok,
    tttLargeFiber60Block0Chunk0Row_9_ok,
    tttLargeFiber60Block0Chunk0Row_10_ok,
    tttLargeFiber60Block0Chunk0Row_11_ok,
    tttLargeFiber60Block0Chunk0Row_12_ok,
    tttLargeFiber60Block0Chunk0Row_13_ok,
    tttLargeFiber60Block0Chunk0Row_14_ok,
    tttLargeFiber60Block0Chunk0Row_15_ok]

def tttLargeFiber60Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber60Block0Chunk0ParentMapCheck 0
    && tttLargeFiber60Block0Chunk0ParentMapCheck 1
    && tttLargeFiber60Block0Chunk0ParentMapCheck 2
    && tttLargeFiber60Block0Chunk0ParentMapCheck 3
    && tttLargeFiber60Block0Chunk0ParentMapCheck 4
    && tttLargeFiber60Block0Chunk0ParentMapCheck 5
    && tttLargeFiber60Block0Chunk0ParentMapCheck 6
    && tttLargeFiber60Block0Chunk0ParentMapCheck 7
    && tttLargeFiber60Block0Chunk0ParentMapCheck 8
    && tttLargeFiber60Block0Chunk0ParentMapCheck 9
    && tttLargeFiber60Block0Chunk0ParentMapCheck 10
    && tttLargeFiber60Block0Chunk0ParentMapCheck 11
    && tttLargeFiber60Block0Chunk0ParentMapCheck 12
    && tttLargeFiber60Block0Chunk0ParentMapCheck 13
    && tttLargeFiber60Block0Chunk0ParentMapCheck 14
    && tttLargeFiber60Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber60Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber60Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber60Block0Chunk0ParentMapAudit,
    tttLargeFiber60Block0Chunk0ParentMap_0_ok,
    tttLargeFiber60Block0Chunk0ParentMap_1_ok,
    tttLargeFiber60Block0Chunk0ParentMap_2_ok,
    tttLargeFiber60Block0Chunk0ParentMap_3_ok,
    tttLargeFiber60Block0Chunk0ParentMap_4_ok,
    tttLargeFiber60Block0Chunk0ParentMap_5_ok,
    tttLargeFiber60Block0Chunk0ParentMap_6_ok,
    tttLargeFiber60Block0Chunk0ParentMap_7_ok,
    tttLargeFiber60Block0Chunk0ParentMap_8_ok,
    tttLargeFiber60Block0Chunk0ParentMap_9_ok,
    tttLargeFiber60Block0Chunk0ParentMap_10_ok,
    tttLargeFiber60Block0Chunk0ParentMap_11_ok,
    tttLargeFiber60Block0Chunk0ParentMap_12_ok,
    tttLargeFiber60Block0Chunk0ParentMap_13_ok,
    tttLargeFiber60Block0Chunk0ParentMap_14_ok,
    tttLargeFiber60Block0Chunk0ParentMap_15_ok]

def tttLargeFiber60Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber60Block0Chunk0ParentPathCheck 0
    && tttLargeFiber60Block0Chunk0ParentPathCheck 1
    && tttLargeFiber60Block0Chunk0ParentPathCheck 2
    && tttLargeFiber60Block0Chunk0ParentPathCheck 3
    && tttLargeFiber60Block0Chunk0ParentPathCheck 4
    && tttLargeFiber60Block0Chunk0ParentPathCheck 5
    && tttLargeFiber60Block0Chunk0ParentPathCheck 6
    && tttLargeFiber60Block0Chunk0ParentPathCheck 7
    && tttLargeFiber60Block0Chunk0ParentPathCheck 8
    && tttLargeFiber60Block0Chunk0ParentPathCheck 9
    && tttLargeFiber60Block0Chunk0ParentPathCheck 10
    && tttLargeFiber60Block0Chunk0ParentPathCheck 11
    && tttLargeFiber60Block0Chunk0ParentPathCheck 12
    && tttLargeFiber60Block0Chunk0ParentPathCheck 13
    && tttLargeFiber60Block0Chunk0ParentPathCheck 14
    && tttLargeFiber60Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber60Block0Chunk0ParentsAudit_ok :
    tttLargeFiber60Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber60Block0Chunk0ParentsAudit,
    tttLargeFiber60Block0Chunk0ParentPath_0_ok,
    tttLargeFiber60Block0Chunk0ParentPath_1_ok,
    tttLargeFiber60Block0Chunk0ParentPath_2_ok,
    tttLargeFiber60Block0Chunk0ParentPath_3_ok,
    tttLargeFiber60Block0Chunk0ParentPath_4_ok,
    tttLargeFiber60Block0Chunk0ParentPath_5_ok,
    tttLargeFiber60Block0Chunk0ParentPath_6_ok,
    tttLargeFiber60Block0Chunk0ParentPath_7_ok,
    tttLargeFiber60Block0Chunk0ParentPath_8_ok,
    tttLargeFiber60Block0Chunk0ParentPath_9_ok,
    tttLargeFiber60Block0Chunk0ParentPath_10_ok,
    tttLargeFiber60Block0Chunk0ParentPath_11_ok,
    tttLargeFiber60Block0Chunk0ParentPath_12_ok,
    tttLargeFiber60Block0Chunk0ParentPath_13_ok,
    tttLargeFiber60Block0Chunk0ParentPath_14_ok,
    tttLargeFiber60Block0Chunk0ParentPath_15_ok]

def tttLargeFiber60Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block0Chunk0SourcesCheck &&
    tttLargeFiber60Block0Chunk0RowsAudit &&
    tttLargeFiber60Block0Chunk0ParentMapAudit &&
    tttLargeFiber60Block0Chunk0ParentsAudit

theorem tttLargeFiber60Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber60Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block0Chunk0SourcesCheck_ok,
    tttLargeFiber60Block0Chunk0RowsAudit_ok,
    tttLargeFiber60Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber60Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
