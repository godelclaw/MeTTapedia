import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block0Chunk0Sources : List Nat :=
  [   4640, 4641, 4642, 4643, 4644, 4645, 4646, 4647,
   4648, 4649, 4650, 4651, 4652, 4653, 4654, 4655]

def tttLargeFiber20Row0 : TripleComponentParentRow :=
  tripleRow 4640 4640 140 148 148 140 148 148
    default
    []

def tttLargeFiber20Row1 : TripleComponentParentRow :=
  tripleRow 4641 4640 140 148 149 140 148 148
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row2 : TripleComponentParentRow :=
  tripleRow 4642 4641 140 148 150 140 148 149
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row3 : TripleComponentParentRow :=
  tripleRow 4643 4640 140 148 151 140 148 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row4 : TripleComponentParentRow :=
  tripleRow 4644 4640 140 148 164 140 148 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row5 : TripleComponentParentRow :=
  tripleRow 4645 4641 140 148 165 140 148 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row6 : TripleComponentParentRow :=
  tripleRow 4646 4644 140 148 166 140 148 164
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row7 : TripleComponentParentRow :=
  tripleRow 4647 4643 140 148 167 140 148 151
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row8 : TripleComponentParentRow :=
  tripleRow 4648 4640 140 149 156 140 148 148
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Row9 : TripleComponentParentRow :=
  tripleRow 4649 4641 140 149 157 140 148 149
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Row10 : TripleComponentParentRow :=
  tripleRow 4650 4642 140 149 158 140 148 150
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Row11 : TripleComponentParentRow :=
  tripleRow 4651 4643 140 149 159 140 148 151
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Row12 : TripleComponentParentRow :=
  tripleRow 4652 4644 140 149 172 140 148 164
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Row13 : TripleComponentParentRow :=
  tripleRow 4653 4645 140 149 173 140 148 165
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Row14 : TripleComponentParentRow :=
  tripleRow 4654 4646 140 149 174 140 148 166
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Row15 : TripleComponentParentRow :=
  tripleRow 4655 4647 140 149 175 140 148 167
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber20Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row0
  , tttLargeFiber20Row1
  , tttLargeFiber20Row2
  , tttLargeFiber20Row3
  , tttLargeFiber20Row4
  , tttLargeFiber20Row5
  , tttLargeFiber20Row6
  , tttLargeFiber20Row7
  , tttLargeFiber20Row8
  , tttLargeFiber20Row9
  , tttLargeFiber20Row10
  , tttLargeFiber20Row11
  , tttLargeFiber20Row12
  , tttLargeFiber20Row13
  , tttLargeFiber20Row14
  , tttLargeFiber20Row15
  ]

def tttLargeFiber20Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber20Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber20Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber20Block0Chunk0Sources

theorem tttLargeFiber20Block0Chunk0SourcesCheck_ok :
    tttLargeFiber20Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber20Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block0Chunk0RowValid
    (listGetD tttLargeFiber20Block0Chunk0Rows i default)

def tttLargeFiber20Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block0Chunk0Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block0Chunk0Sources 0 0 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (0 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block0Chunk0Sources 1 0 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (1 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block0Chunk0Sources 2 0 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block0Chunk0Sources 3 0 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (1 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block0Chunk0Sources 4 0 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (1 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block0Chunk0Sources 5 0 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block0Chunk0Sources 6 0 == 4646
      && tttLargeFiber20ParentOf 4646 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block0Chunk0Sources 7 0 == 4647
      && tttLargeFiber20ParentOf 4647 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block0Chunk0Sources 8 0 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (1 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block0Chunk0Sources 9 0 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block0Chunk0Sources 10 0 == 4650
      && tttLargeFiber20ParentOf 4650 == 4642
      && tttLargeFiber20ParentOf 4642 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block0Chunk0Sources 11 0 == 4651
      && tttLargeFiber20ParentOf 4651 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block0Chunk0Sources 12 0 == 4652
      && tttLargeFiber20ParentOf 4652 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block0Chunk0Sources 13 0 == 4653
      && tttLargeFiber20ParentOf 4653 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block0Chunk0Sources 14 0 == 4654
      && tttLargeFiber20ParentOf 4654 == 4646
      && tttLargeFiber20ParentOf 4646 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block0Chunk0Sources 15 0 == 4655
      && tttLargeFiber20ParentOf 4655 == 4647
      && tttLargeFiber20ParentOf 4647 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block0Chunk0Row_0_ok :
    tttLargeFiber20Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_1_ok :
    tttLargeFiber20Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_2_ok :
    tttLargeFiber20Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_3_ok :
    tttLargeFiber20Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_4_ok :
    tttLargeFiber20Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_5_ok :
    tttLargeFiber20Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_6_ok :
    tttLargeFiber20Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_7_ok :
    tttLargeFiber20Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_8_ok :
    tttLargeFiber20Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_9_ok :
    tttLargeFiber20Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_10_ok :
    tttLargeFiber20Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_11_ok :
    tttLargeFiber20Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_12_ok :
    tttLargeFiber20Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_13_ok :
    tttLargeFiber20Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_14_ok :
    tttLargeFiber20Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0Row_15_ok :
    tttLargeFiber20Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_0_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_1_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_2_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_3_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_4_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_5_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_6_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_7_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_8_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_9_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_10_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_11_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_12_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_13_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_14_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentMap_15_ok :
    tttLargeFiber20Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_0_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_1_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_2_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_3_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_4_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_5_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_6_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_7_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_8_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_9_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_10_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_11_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_12_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_13_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_14_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block0Chunk0ParentPath_15_ok :
    tttLargeFiber20Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber20Block0Chunk0RowCheck 0
    && tttLargeFiber20Block0Chunk0RowCheck 1
    && tttLargeFiber20Block0Chunk0RowCheck 2
    && tttLargeFiber20Block0Chunk0RowCheck 3
    && tttLargeFiber20Block0Chunk0RowCheck 4
    && tttLargeFiber20Block0Chunk0RowCheck 5
    && tttLargeFiber20Block0Chunk0RowCheck 6
    && tttLargeFiber20Block0Chunk0RowCheck 7
    && tttLargeFiber20Block0Chunk0RowCheck 8
    && tttLargeFiber20Block0Chunk0RowCheck 9
    && tttLargeFiber20Block0Chunk0RowCheck 10
    && tttLargeFiber20Block0Chunk0RowCheck 11
    && tttLargeFiber20Block0Chunk0RowCheck 12
    && tttLargeFiber20Block0Chunk0RowCheck 13
    && tttLargeFiber20Block0Chunk0RowCheck 14
    && tttLargeFiber20Block0Chunk0RowCheck 15

theorem tttLargeFiber20Block0Chunk0RowsAudit_ok :
    tttLargeFiber20Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber20Block0Chunk0RowsAudit,
    tttLargeFiber20Block0Chunk0Row_0_ok,
    tttLargeFiber20Block0Chunk0Row_1_ok,
    tttLargeFiber20Block0Chunk0Row_2_ok,
    tttLargeFiber20Block0Chunk0Row_3_ok,
    tttLargeFiber20Block0Chunk0Row_4_ok,
    tttLargeFiber20Block0Chunk0Row_5_ok,
    tttLargeFiber20Block0Chunk0Row_6_ok,
    tttLargeFiber20Block0Chunk0Row_7_ok,
    tttLargeFiber20Block0Chunk0Row_8_ok,
    tttLargeFiber20Block0Chunk0Row_9_ok,
    tttLargeFiber20Block0Chunk0Row_10_ok,
    tttLargeFiber20Block0Chunk0Row_11_ok,
    tttLargeFiber20Block0Chunk0Row_12_ok,
    tttLargeFiber20Block0Chunk0Row_13_ok,
    tttLargeFiber20Block0Chunk0Row_14_ok,
    tttLargeFiber20Block0Chunk0Row_15_ok]

def tttLargeFiber20Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber20Block0Chunk0ParentMapCheck 0
    && tttLargeFiber20Block0Chunk0ParentMapCheck 1
    && tttLargeFiber20Block0Chunk0ParentMapCheck 2
    && tttLargeFiber20Block0Chunk0ParentMapCheck 3
    && tttLargeFiber20Block0Chunk0ParentMapCheck 4
    && tttLargeFiber20Block0Chunk0ParentMapCheck 5
    && tttLargeFiber20Block0Chunk0ParentMapCheck 6
    && tttLargeFiber20Block0Chunk0ParentMapCheck 7
    && tttLargeFiber20Block0Chunk0ParentMapCheck 8
    && tttLargeFiber20Block0Chunk0ParentMapCheck 9
    && tttLargeFiber20Block0Chunk0ParentMapCheck 10
    && tttLargeFiber20Block0Chunk0ParentMapCheck 11
    && tttLargeFiber20Block0Chunk0ParentMapCheck 12
    && tttLargeFiber20Block0Chunk0ParentMapCheck 13
    && tttLargeFiber20Block0Chunk0ParentMapCheck 14
    && tttLargeFiber20Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber20Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber20Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber20Block0Chunk0ParentMapAudit,
    tttLargeFiber20Block0Chunk0ParentMap_0_ok,
    tttLargeFiber20Block0Chunk0ParentMap_1_ok,
    tttLargeFiber20Block0Chunk0ParentMap_2_ok,
    tttLargeFiber20Block0Chunk0ParentMap_3_ok,
    tttLargeFiber20Block0Chunk0ParentMap_4_ok,
    tttLargeFiber20Block0Chunk0ParentMap_5_ok,
    tttLargeFiber20Block0Chunk0ParentMap_6_ok,
    tttLargeFiber20Block0Chunk0ParentMap_7_ok,
    tttLargeFiber20Block0Chunk0ParentMap_8_ok,
    tttLargeFiber20Block0Chunk0ParentMap_9_ok,
    tttLargeFiber20Block0Chunk0ParentMap_10_ok,
    tttLargeFiber20Block0Chunk0ParentMap_11_ok,
    tttLargeFiber20Block0Chunk0ParentMap_12_ok,
    tttLargeFiber20Block0Chunk0ParentMap_13_ok,
    tttLargeFiber20Block0Chunk0ParentMap_14_ok,
    tttLargeFiber20Block0Chunk0ParentMap_15_ok]

def tttLargeFiber20Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber20Block0Chunk0ParentPathCheck 0
    && tttLargeFiber20Block0Chunk0ParentPathCheck 1
    && tttLargeFiber20Block0Chunk0ParentPathCheck 2
    && tttLargeFiber20Block0Chunk0ParentPathCheck 3
    && tttLargeFiber20Block0Chunk0ParentPathCheck 4
    && tttLargeFiber20Block0Chunk0ParentPathCheck 5
    && tttLargeFiber20Block0Chunk0ParentPathCheck 6
    && tttLargeFiber20Block0Chunk0ParentPathCheck 7
    && tttLargeFiber20Block0Chunk0ParentPathCheck 8
    && tttLargeFiber20Block0Chunk0ParentPathCheck 9
    && tttLargeFiber20Block0Chunk0ParentPathCheck 10
    && tttLargeFiber20Block0Chunk0ParentPathCheck 11
    && tttLargeFiber20Block0Chunk0ParentPathCheck 12
    && tttLargeFiber20Block0Chunk0ParentPathCheck 13
    && tttLargeFiber20Block0Chunk0ParentPathCheck 14
    && tttLargeFiber20Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber20Block0Chunk0ParentsAudit_ok :
    tttLargeFiber20Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber20Block0Chunk0ParentsAudit,
    tttLargeFiber20Block0Chunk0ParentPath_0_ok,
    tttLargeFiber20Block0Chunk0ParentPath_1_ok,
    tttLargeFiber20Block0Chunk0ParentPath_2_ok,
    tttLargeFiber20Block0Chunk0ParentPath_3_ok,
    tttLargeFiber20Block0Chunk0ParentPath_4_ok,
    tttLargeFiber20Block0Chunk0ParentPath_5_ok,
    tttLargeFiber20Block0Chunk0ParentPath_6_ok,
    tttLargeFiber20Block0Chunk0ParentPath_7_ok,
    tttLargeFiber20Block0Chunk0ParentPath_8_ok,
    tttLargeFiber20Block0Chunk0ParentPath_9_ok,
    tttLargeFiber20Block0Chunk0ParentPath_10_ok,
    tttLargeFiber20Block0Chunk0ParentPath_11_ok,
    tttLargeFiber20Block0Chunk0ParentPath_12_ok,
    tttLargeFiber20Block0Chunk0ParentPath_13_ok,
    tttLargeFiber20Block0Chunk0ParentPath_14_ok,
    tttLargeFiber20Block0Chunk0ParentPath_15_ok]

def tttLargeFiber20Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block0Chunk0SourcesCheck &&
    tttLargeFiber20Block0Chunk0RowsAudit &&
    tttLargeFiber20Block0Chunk0ParentMapAudit &&
    tttLargeFiber20Block0Chunk0ParentsAudit

theorem tttLargeFiber20Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber20Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block0Chunk0SourcesCheck_ok,
    tttLargeFiber20Block0Chunk0RowsAudit_ok,
    tttLargeFiber20Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber20Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
