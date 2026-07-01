import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 70, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber70Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber70Data

def tttLargeFiber70Block0Chunk0Sources : List Nat :=
  [   2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727,
   2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]

def tttLargeFiber70Row0 : TripleComponentParentRow :=
  tripleRow 2720 2720 80 80 80 80 80 80
    default
    []

def tttLargeFiber70Row1 : TripleComponentParentRow :=
  tripleRow 2721 2720 80 80 81 80 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row2 : TripleComponentParentRow :=
  tripleRow 2722 2720 80 80 82 80 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row3 : TripleComponentParentRow :=
  tripleRow 2723 2721 80 80 83 80 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row4 : TripleComponentParentRow :=
  tripleRow 2724 2722 80 80 100 80 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row5 : TripleComponentParentRow :=
  tripleRow 2725 2727 80 80 101 80 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber70Row6 : TripleComponentParentRow :=
  tripleRow 2726 2721 80 80 102 80 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber70Row7 : TripleComponentParentRow :=
  tripleRow 2727 2720 80 80 103 80 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber70Row8 : TripleComponentParentRow :=
  tripleRow 2728 2720 80 81 88 80 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Row9 : TripleComponentParentRow :=
  tripleRow 2729 2721 80 81 89 80 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Row10 : TripleComponentParentRow :=
  tripleRow 2730 2722 80 81 90 80 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Row11 : TripleComponentParentRow :=
  tripleRow 2731 2723 80 81 91 80 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Row12 : TripleComponentParentRow :=
  tripleRow 2732 2724 80 81 108 80 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Row13 : TripleComponentParentRow :=
  tripleRow 2733 2725 80 81 109 80 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Row14 : TripleComponentParentRow :=
  tripleRow 2734 2726 80 81 110 80 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Row15 : TripleComponentParentRow :=
  tripleRow 2735 2727 80 81 111 80 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber70Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber70Row0
  , tttLargeFiber70Row1
  , tttLargeFiber70Row2
  , tttLargeFiber70Row3
  , tttLargeFiber70Row4
  , tttLargeFiber70Row5
  , tttLargeFiber70Row6
  , tttLargeFiber70Row7
  , tttLargeFiber70Row8
  , tttLargeFiber70Row9
  , tttLargeFiber70Row10
  , tttLargeFiber70Row11
  , tttLargeFiber70Row12
  , tttLargeFiber70Row13
  , tttLargeFiber70Row14
  , tttLargeFiber70Row15
  ]

def tttLargeFiber70Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2720 <= i) && decide (i < 2976)) ||
    (decide (3280 <= i) && decide (i < 3536))

def tttLargeFiber70Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber70Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber70Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber70Key &&
          chainInputKey tttWord t == tttLargeFiber70Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber70Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber70Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber70Block0Chunk0Sources

theorem tttLargeFiber70Block0Chunk0SourcesCheck_ok :
    tttLargeFiber70Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber70Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber70Block0Chunk0RowValid
    (listGetD tttLargeFiber70Block0Chunk0Rows i default)

def tttLargeFiber70Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber70Block0Chunk0Rows i default
  row.parent == tttLargeFiber70ParentOf row.source

def tttLargeFiber70Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber70Block0Chunk0Sources 0 0 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (0 <= tttLargeFiber70MaxParentDepth)
  | 1 => listGetD tttLargeFiber70Block0Chunk0Sources 1 0 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (1 <= tttLargeFiber70MaxParentDepth)
  | 2 => listGetD tttLargeFiber70Block0Chunk0Sources 2 0 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (1 <= tttLargeFiber70MaxParentDepth)
  | 3 => listGetD tttLargeFiber70Block0Chunk0Sources 3 0 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 4 => listGetD tttLargeFiber70Block0Chunk0Sources 4 0 == 2724
      && tttLargeFiber70ParentOf 2724 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 5 => listGetD tttLargeFiber70Block0Chunk0Sources 5 0 == 2725
      && tttLargeFiber70ParentOf 2725 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 6 => listGetD tttLargeFiber70Block0Chunk0Sources 6 0 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 7 => listGetD tttLargeFiber70Block0Chunk0Sources 7 0 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (1 <= tttLargeFiber70MaxParentDepth)
  | 8 => listGetD tttLargeFiber70Block0Chunk0Sources 8 0 == 2728
      && tttLargeFiber70ParentOf 2728 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (1 <= tttLargeFiber70MaxParentDepth)
  | 9 => listGetD tttLargeFiber70Block0Chunk0Sources 9 0 == 2729
      && tttLargeFiber70ParentOf 2729 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 10 => listGetD tttLargeFiber70Block0Chunk0Sources 10 0 == 2730
      && tttLargeFiber70ParentOf 2730 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | 11 => listGetD tttLargeFiber70Block0Chunk0Sources 11 0 == 2731
      && tttLargeFiber70ParentOf 2731 == 2723
      && tttLargeFiber70ParentOf 2723 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 12 => listGetD tttLargeFiber70Block0Chunk0Sources 12 0 == 2732
      && tttLargeFiber70ParentOf 2732 == 2724
      && tttLargeFiber70ParentOf 2724 == 2722
      && tttLargeFiber70ParentOf 2722 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 13 => listGetD tttLargeFiber70Block0Chunk0Sources 13 0 == 2733
      && tttLargeFiber70ParentOf 2733 == 2725
      && tttLargeFiber70ParentOf 2725 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 14 => listGetD tttLargeFiber70Block0Chunk0Sources 14 0 == 2734
      && tttLargeFiber70ParentOf 2734 == 2726
      && tttLargeFiber70ParentOf 2726 == 2721
      && tttLargeFiber70ParentOf 2721 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (3 <= tttLargeFiber70MaxParentDepth)
  | 15 => listGetD tttLargeFiber70Block0Chunk0Sources 15 0 == 2735
      && tttLargeFiber70ParentOf 2735 == 2727
      && tttLargeFiber70ParentOf 2727 == 2720
      && 2720 == tttLargeFiber70Root
      && decide (2 <= tttLargeFiber70MaxParentDepth)
  | _ => false

theorem tttLargeFiber70Block0Chunk0Row_0_ok :
    tttLargeFiber70Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_1_ok :
    tttLargeFiber70Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_2_ok :
    tttLargeFiber70Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_3_ok :
    tttLargeFiber70Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_4_ok :
    tttLargeFiber70Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_5_ok :
    tttLargeFiber70Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_6_ok :
    tttLargeFiber70Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_7_ok :
    tttLargeFiber70Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_8_ok :
    tttLargeFiber70Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_9_ok :
    tttLargeFiber70Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_10_ok :
    tttLargeFiber70Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_11_ok :
    tttLargeFiber70Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_12_ok :
    tttLargeFiber70Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_13_ok :
    tttLargeFiber70Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_14_ok :
    tttLargeFiber70Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0Row_15_ok :
    tttLargeFiber70Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_0_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_1_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_2_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_3_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_4_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_5_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_6_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_7_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_8_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_9_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_10_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_11_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_12_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_13_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_14_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentMap_15_ok :
    tttLargeFiber70Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_0_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_1_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_2_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_3_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_4_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_5_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_6_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_7_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_8_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_9_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_10_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_11_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_12_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_13_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_14_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber70Block0Chunk0ParentPath_15_ok :
    tttLargeFiber70Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber70Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber70Block0Chunk0RowCheck 0
    && tttLargeFiber70Block0Chunk0RowCheck 1
    && tttLargeFiber70Block0Chunk0RowCheck 2
    && tttLargeFiber70Block0Chunk0RowCheck 3
    && tttLargeFiber70Block0Chunk0RowCheck 4
    && tttLargeFiber70Block0Chunk0RowCheck 5
    && tttLargeFiber70Block0Chunk0RowCheck 6
    && tttLargeFiber70Block0Chunk0RowCheck 7
    && tttLargeFiber70Block0Chunk0RowCheck 8
    && tttLargeFiber70Block0Chunk0RowCheck 9
    && tttLargeFiber70Block0Chunk0RowCheck 10
    && tttLargeFiber70Block0Chunk0RowCheck 11
    && tttLargeFiber70Block0Chunk0RowCheck 12
    && tttLargeFiber70Block0Chunk0RowCheck 13
    && tttLargeFiber70Block0Chunk0RowCheck 14
    && tttLargeFiber70Block0Chunk0RowCheck 15

theorem tttLargeFiber70Block0Chunk0RowsAudit_ok :
    tttLargeFiber70Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber70Block0Chunk0RowsAudit,
    tttLargeFiber70Block0Chunk0Row_0_ok,
    tttLargeFiber70Block0Chunk0Row_1_ok,
    tttLargeFiber70Block0Chunk0Row_2_ok,
    tttLargeFiber70Block0Chunk0Row_3_ok,
    tttLargeFiber70Block0Chunk0Row_4_ok,
    tttLargeFiber70Block0Chunk0Row_5_ok,
    tttLargeFiber70Block0Chunk0Row_6_ok,
    tttLargeFiber70Block0Chunk0Row_7_ok,
    tttLargeFiber70Block0Chunk0Row_8_ok,
    tttLargeFiber70Block0Chunk0Row_9_ok,
    tttLargeFiber70Block0Chunk0Row_10_ok,
    tttLargeFiber70Block0Chunk0Row_11_ok,
    tttLargeFiber70Block0Chunk0Row_12_ok,
    tttLargeFiber70Block0Chunk0Row_13_ok,
    tttLargeFiber70Block0Chunk0Row_14_ok,
    tttLargeFiber70Block0Chunk0Row_15_ok]

def tttLargeFiber70Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber70Block0Chunk0ParentMapCheck 0
    && tttLargeFiber70Block0Chunk0ParentMapCheck 1
    && tttLargeFiber70Block0Chunk0ParentMapCheck 2
    && tttLargeFiber70Block0Chunk0ParentMapCheck 3
    && tttLargeFiber70Block0Chunk0ParentMapCheck 4
    && tttLargeFiber70Block0Chunk0ParentMapCheck 5
    && tttLargeFiber70Block0Chunk0ParentMapCheck 6
    && tttLargeFiber70Block0Chunk0ParentMapCheck 7
    && tttLargeFiber70Block0Chunk0ParentMapCheck 8
    && tttLargeFiber70Block0Chunk0ParentMapCheck 9
    && tttLargeFiber70Block0Chunk0ParentMapCheck 10
    && tttLargeFiber70Block0Chunk0ParentMapCheck 11
    && tttLargeFiber70Block0Chunk0ParentMapCheck 12
    && tttLargeFiber70Block0Chunk0ParentMapCheck 13
    && tttLargeFiber70Block0Chunk0ParentMapCheck 14
    && tttLargeFiber70Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber70Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber70Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber70Block0Chunk0ParentMapAudit,
    tttLargeFiber70Block0Chunk0ParentMap_0_ok,
    tttLargeFiber70Block0Chunk0ParentMap_1_ok,
    tttLargeFiber70Block0Chunk0ParentMap_2_ok,
    tttLargeFiber70Block0Chunk0ParentMap_3_ok,
    tttLargeFiber70Block0Chunk0ParentMap_4_ok,
    tttLargeFiber70Block0Chunk0ParentMap_5_ok,
    tttLargeFiber70Block0Chunk0ParentMap_6_ok,
    tttLargeFiber70Block0Chunk0ParentMap_7_ok,
    tttLargeFiber70Block0Chunk0ParentMap_8_ok,
    tttLargeFiber70Block0Chunk0ParentMap_9_ok,
    tttLargeFiber70Block0Chunk0ParentMap_10_ok,
    tttLargeFiber70Block0Chunk0ParentMap_11_ok,
    tttLargeFiber70Block0Chunk0ParentMap_12_ok,
    tttLargeFiber70Block0Chunk0ParentMap_13_ok,
    tttLargeFiber70Block0Chunk0ParentMap_14_ok,
    tttLargeFiber70Block0Chunk0ParentMap_15_ok]

def tttLargeFiber70Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber70Block0Chunk0ParentPathCheck 0
    && tttLargeFiber70Block0Chunk0ParentPathCheck 1
    && tttLargeFiber70Block0Chunk0ParentPathCheck 2
    && tttLargeFiber70Block0Chunk0ParentPathCheck 3
    && tttLargeFiber70Block0Chunk0ParentPathCheck 4
    && tttLargeFiber70Block0Chunk0ParentPathCheck 5
    && tttLargeFiber70Block0Chunk0ParentPathCheck 6
    && tttLargeFiber70Block0Chunk0ParentPathCheck 7
    && tttLargeFiber70Block0Chunk0ParentPathCheck 8
    && tttLargeFiber70Block0Chunk0ParentPathCheck 9
    && tttLargeFiber70Block0Chunk0ParentPathCheck 10
    && tttLargeFiber70Block0Chunk0ParentPathCheck 11
    && tttLargeFiber70Block0Chunk0ParentPathCheck 12
    && tttLargeFiber70Block0Chunk0ParentPathCheck 13
    && tttLargeFiber70Block0Chunk0ParentPathCheck 14
    && tttLargeFiber70Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber70Block0Chunk0ParentsAudit_ok :
    tttLargeFiber70Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber70Block0Chunk0ParentsAudit,
    tttLargeFiber70Block0Chunk0ParentPath_0_ok,
    tttLargeFiber70Block0Chunk0ParentPath_1_ok,
    tttLargeFiber70Block0Chunk0ParentPath_2_ok,
    tttLargeFiber70Block0Chunk0ParentPath_3_ok,
    tttLargeFiber70Block0Chunk0ParentPath_4_ok,
    tttLargeFiber70Block0Chunk0ParentPath_5_ok,
    tttLargeFiber70Block0Chunk0ParentPath_6_ok,
    tttLargeFiber70Block0Chunk0ParentPath_7_ok,
    tttLargeFiber70Block0Chunk0ParentPath_8_ok,
    tttLargeFiber70Block0Chunk0ParentPath_9_ok,
    tttLargeFiber70Block0Chunk0ParentPath_10_ok,
    tttLargeFiber70Block0Chunk0ParentPath_11_ok,
    tttLargeFiber70Block0Chunk0ParentPath_12_ok,
    tttLargeFiber70Block0Chunk0ParentPath_13_ok,
    tttLargeFiber70Block0Chunk0ParentPath_14_ok,
    tttLargeFiber70Block0Chunk0ParentPath_15_ok]

def tttLargeFiber70Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber70CountsAudit &&
    tttLargeFiber70Block0Chunk0SourcesCheck &&
    tttLargeFiber70Block0Chunk0RowsAudit &&
    tttLargeFiber70Block0Chunk0ParentMapAudit &&
    tttLargeFiber70Block0Chunk0ParentsAudit

theorem tttLargeFiber70Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber70Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber70Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber70CountsAudit_ok,
    tttLargeFiber70Block0Chunk0SourcesCheck_ok,
    tttLargeFiber70Block0Chunk0RowsAudit_ok,
    tttLargeFiber70Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber70Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber70Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
