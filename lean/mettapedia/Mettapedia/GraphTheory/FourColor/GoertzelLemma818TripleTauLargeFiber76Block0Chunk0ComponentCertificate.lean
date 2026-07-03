import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block0Chunk0Sources : List Nat :=
  [   2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999,
   3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007]

def tttLargeFiber76Row0 : TripleComponentParentRow :=
  tripleRow 2992 2992 88 80 80 88 80 80
    default
    []

def tttLargeFiber76Row1 : TripleComponentParentRow :=
  tripleRow 2993 2992 88 80 81 88 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row2 : TripleComponentParentRow :=
  tripleRow 2994 2992 88 80 82 88 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row3 : TripleComponentParentRow :=
  tripleRow 2995 2993 88 80 83 88 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row4 : TripleComponentParentRow :=
  tripleRow 2996 2994 88 80 100 88 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row5 : TripleComponentParentRow :=
  tripleRow 2997 2999 88 80 101 88 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row6 : TripleComponentParentRow :=
  tripleRow 2998 2993 88 80 102 88 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row7 : TripleComponentParentRow :=
  tripleRow 2999 2992 88 80 103 88 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row8 : TripleComponentParentRow :=
  tripleRow 3000 2992 88 81 88 88 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Row9 : TripleComponentParentRow :=
  tripleRow 3001 2993 88 81 89 88 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Row10 : TripleComponentParentRow :=
  tripleRow 3002 2994 88 81 90 88 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Row11 : TripleComponentParentRow :=
  tripleRow 3003 2995 88 81 91 88 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Row12 : TripleComponentParentRow :=
  tripleRow 3004 2996 88 81 108 88 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Row13 : TripleComponentParentRow :=
  tripleRow 3005 2997 88 81 109 88 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Row14 : TripleComponentParentRow :=
  tripleRow 3006 2998 88 81 110 88 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Row15 : TripleComponentParentRow :=
  tripleRow 3007 2999 88 81 111 88 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber76Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row0
  , tttLargeFiber76Row1
  , tttLargeFiber76Row2
  , tttLargeFiber76Row3
  , tttLargeFiber76Row4
  , tttLargeFiber76Row5
  , tttLargeFiber76Row6
  , tttLargeFiber76Row7
  , tttLargeFiber76Row8
  , tttLargeFiber76Row9
  , tttLargeFiber76Row10
  , tttLargeFiber76Row11
  , tttLargeFiber76Row12
  , tttLargeFiber76Row13
  , tttLargeFiber76Row14
  , tttLargeFiber76Row15
  ]

def tttLargeFiber76Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber76Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber76Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber76Block0Chunk0Sources

theorem tttLargeFiber76Block0Chunk0SourcesCheck_ok :
    tttLargeFiber76Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber76Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block0Chunk0RowValid
    (listGetD tttLargeFiber76Block0Chunk0Rows i default)

def tttLargeFiber76Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block0Chunk0Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block0Chunk0Sources 0 0 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (0 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block0Chunk0Sources 1 0 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (1 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block0Chunk0Sources 2 0 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (1 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block0Chunk0Sources 3 0 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block0Chunk0Sources 4 0 == 2996
      && tttLargeFiber76ParentOf 2996 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block0Chunk0Sources 5 0 == 2997
      && tttLargeFiber76ParentOf 2997 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block0Chunk0Sources 6 0 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block0Chunk0Sources 7 0 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (1 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block0Chunk0Sources 8 0 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (1 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block0Chunk0Sources 9 0 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block0Chunk0Sources 10 0 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block0Chunk0Sources 11 0 == 3003
      && tttLargeFiber76ParentOf 3003 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block0Chunk0Sources 12 0 == 3004
      && tttLargeFiber76ParentOf 3004 == 2996
      && tttLargeFiber76ParentOf 2996 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block0Chunk0Sources 13 0 == 3005
      && tttLargeFiber76ParentOf 3005 == 2997
      && tttLargeFiber76ParentOf 2997 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block0Chunk0Sources 14 0 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block0Chunk0Sources 15 0 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block0Chunk0Row_0_ok :
    tttLargeFiber76Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_1_ok :
    tttLargeFiber76Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_2_ok :
    tttLargeFiber76Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_3_ok :
    tttLargeFiber76Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_4_ok :
    tttLargeFiber76Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_5_ok :
    tttLargeFiber76Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_6_ok :
    tttLargeFiber76Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_7_ok :
    tttLargeFiber76Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_8_ok :
    tttLargeFiber76Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_9_ok :
    tttLargeFiber76Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_10_ok :
    tttLargeFiber76Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_11_ok :
    tttLargeFiber76Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_12_ok :
    tttLargeFiber76Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_13_ok :
    tttLargeFiber76Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_14_ok :
    tttLargeFiber76Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0Row_15_ok :
    tttLargeFiber76Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_0_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_1_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_2_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_3_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_4_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_5_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_6_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_7_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_8_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_9_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_10_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_11_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_12_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_13_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_14_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentMap_15_ok :
    tttLargeFiber76Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_0_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_1_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_2_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_3_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_4_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_5_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_6_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_7_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_8_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_9_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_10_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_11_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_12_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_13_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_14_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block0Chunk0ParentPath_15_ok :
    tttLargeFiber76Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber76Block0Chunk0RowCheck 0
    && tttLargeFiber76Block0Chunk0RowCheck 1
    && tttLargeFiber76Block0Chunk0RowCheck 2
    && tttLargeFiber76Block0Chunk0RowCheck 3
    && tttLargeFiber76Block0Chunk0RowCheck 4
    && tttLargeFiber76Block0Chunk0RowCheck 5
    && tttLargeFiber76Block0Chunk0RowCheck 6
    && tttLargeFiber76Block0Chunk0RowCheck 7
    && tttLargeFiber76Block0Chunk0RowCheck 8
    && tttLargeFiber76Block0Chunk0RowCheck 9
    && tttLargeFiber76Block0Chunk0RowCheck 10
    && tttLargeFiber76Block0Chunk0RowCheck 11
    && tttLargeFiber76Block0Chunk0RowCheck 12
    && tttLargeFiber76Block0Chunk0RowCheck 13
    && tttLargeFiber76Block0Chunk0RowCheck 14
    && tttLargeFiber76Block0Chunk0RowCheck 15

theorem tttLargeFiber76Block0Chunk0RowsAudit_ok :
    tttLargeFiber76Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber76Block0Chunk0RowsAudit,
    tttLargeFiber76Block0Chunk0Row_0_ok,
    tttLargeFiber76Block0Chunk0Row_1_ok,
    tttLargeFiber76Block0Chunk0Row_2_ok,
    tttLargeFiber76Block0Chunk0Row_3_ok,
    tttLargeFiber76Block0Chunk0Row_4_ok,
    tttLargeFiber76Block0Chunk0Row_5_ok,
    tttLargeFiber76Block0Chunk0Row_6_ok,
    tttLargeFiber76Block0Chunk0Row_7_ok,
    tttLargeFiber76Block0Chunk0Row_8_ok,
    tttLargeFiber76Block0Chunk0Row_9_ok,
    tttLargeFiber76Block0Chunk0Row_10_ok,
    tttLargeFiber76Block0Chunk0Row_11_ok,
    tttLargeFiber76Block0Chunk0Row_12_ok,
    tttLargeFiber76Block0Chunk0Row_13_ok,
    tttLargeFiber76Block0Chunk0Row_14_ok,
    tttLargeFiber76Block0Chunk0Row_15_ok]

def tttLargeFiber76Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber76Block0Chunk0ParentMapCheck 0
    && tttLargeFiber76Block0Chunk0ParentMapCheck 1
    && tttLargeFiber76Block0Chunk0ParentMapCheck 2
    && tttLargeFiber76Block0Chunk0ParentMapCheck 3
    && tttLargeFiber76Block0Chunk0ParentMapCheck 4
    && tttLargeFiber76Block0Chunk0ParentMapCheck 5
    && tttLargeFiber76Block0Chunk0ParentMapCheck 6
    && tttLargeFiber76Block0Chunk0ParentMapCheck 7
    && tttLargeFiber76Block0Chunk0ParentMapCheck 8
    && tttLargeFiber76Block0Chunk0ParentMapCheck 9
    && tttLargeFiber76Block0Chunk0ParentMapCheck 10
    && tttLargeFiber76Block0Chunk0ParentMapCheck 11
    && tttLargeFiber76Block0Chunk0ParentMapCheck 12
    && tttLargeFiber76Block0Chunk0ParentMapCheck 13
    && tttLargeFiber76Block0Chunk0ParentMapCheck 14
    && tttLargeFiber76Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber76Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber76Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber76Block0Chunk0ParentMapAudit,
    tttLargeFiber76Block0Chunk0ParentMap_0_ok,
    tttLargeFiber76Block0Chunk0ParentMap_1_ok,
    tttLargeFiber76Block0Chunk0ParentMap_2_ok,
    tttLargeFiber76Block0Chunk0ParentMap_3_ok,
    tttLargeFiber76Block0Chunk0ParentMap_4_ok,
    tttLargeFiber76Block0Chunk0ParentMap_5_ok,
    tttLargeFiber76Block0Chunk0ParentMap_6_ok,
    tttLargeFiber76Block0Chunk0ParentMap_7_ok,
    tttLargeFiber76Block0Chunk0ParentMap_8_ok,
    tttLargeFiber76Block0Chunk0ParentMap_9_ok,
    tttLargeFiber76Block0Chunk0ParentMap_10_ok,
    tttLargeFiber76Block0Chunk0ParentMap_11_ok,
    tttLargeFiber76Block0Chunk0ParentMap_12_ok,
    tttLargeFiber76Block0Chunk0ParentMap_13_ok,
    tttLargeFiber76Block0Chunk0ParentMap_14_ok,
    tttLargeFiber76Block0Chunk0ParentMap_15_ok]

def tttLargeFiber76Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber76Block0Chunk0ParentPathCheck 0
    && tttLargeFiber76Block0Chunk0ParentPathCheck 1
    && tttLargeFiber76Block0Chunk0ParentPathCheck 2
    && tttLargeFiber76Block0Chunk0ParentPathCheck 3
    && tttLargeFiber76Block0Chunk0ParentPathCheck 4
    && tttLargeFiber76Block0Chunk0ParentPathCheck 5
    && tttLargeFiber76Block0Chunk0ParentPathCheck 6
    && tttLargeFiber76Block0Chunk0ParentPathCheck 7
    && tttLargeFiber76Block0Chunk0ParentPathCheck 8
    && tttLargeFiber76Block0Chunk0ParentPathCheck 9
    && tttLargeFiber76Block0Chunk0ParentPathCheck 10
    && tttLargeFiber76Block0Chunk0ParentPathCheck 11
    && tttLargeFiber76Block0Chunk0ParentPathCheck 12
    && tttLargeFiber76Block0Chunk0ParentPathCheck 13
    && tttLargeFiber76Block0Chunk0ParentPathCheck 14
    && tttLargeFiber76Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber76Block0Chunk0ParentsAudit_ok :
    tttLargeFiber76Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber76Block0Chunk0ParentsAudit,
    tttLargeFiber76Block0Chunk0ParentPath_0_ok,
    tttLargeFiber76Block0Chunk0ParentPath_1_ok,
    tttLargeFiber76Block0Chunk0ParentPath_2_ok,
    tttLargeFiber76Block0Chunk0ParentPath_3_ok,
    tttLargeFiber76Block0Chunk0ParentPath_4_ok,
    tttLargeFiber76Block0Chunk0ParentPath_5_ok,
    tttLargeFiber76Block0Chunk0ParentPath_6_ok,
    tttLargeFiber76Block0Chunk0ParentPath_7_ok,
    tttLargeFiber76Block0Chunk0ParentPath_8_ok,
    tttLargeFiber76Block0Chunk0ParentPath_9_ok,
    tttLargeFiber76Block0Chunk0ParentPath_10_ok,
    tttLargeFiber76Block0Chunk0ParentPath_11_ok,
    tttLargeFiber76Block0Chunk0ParentPath_12_ok,
    tttLargeFiber76Block0Chunk0ParentPath_13_ok,
    tttLargeFiber76Block0Chunk0ParentPath_14_ok,
    tttLargeFiber76Block0Chunk0ParentPath_15_ok]

def tttLargeFiber76Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block0Chunk0SourcesCheck &&
    tttLargeFiber76Block0Chunk0RowsAudit &&
    tttLargeFiber76Block0Chunk0ParentMapAudit &&
    tttLargeFiber76Block0Chunk0ParentsAudit

theorem tttLargeFiber76Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber76Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block0Chunk0SourcesCheck_ok,
    tttLargeFiber76Block0Chunk0RowsAudit_ok,
    tttLargeFiber76Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber76Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
