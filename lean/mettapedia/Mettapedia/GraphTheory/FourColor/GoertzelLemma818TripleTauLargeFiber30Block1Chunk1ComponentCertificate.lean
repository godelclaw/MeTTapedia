import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block1Chunk1Sources : List Nat :=
  [   80, 81, 82, 83, 84, 85, 86, 87,
   88, 89, 90, 91, 92, 93, 94, 95]

def tttLargeFiber30Row80 : TripleComponentParentRow :=
  tripleRow 80 16 1 90 16 0 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row81 : TripleComponentParentRow :=
  tripleRow 81 17 1 90 17 0 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row82 : TripleComponentParentRow :=
  tripleRow 82 18 1 90 18 0 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row83 : TripleComponentParentRow :=
  tripleRow 83 19 1 90 19 0 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row84 : TripleComponentParentRow :=
  tripleRow 84 20 1 90 32 0 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row85 : TripleComponentParentRow :=
  tripleRow 85 21 1 90 33 0 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row86 : TripleComponentParentRow :=
  tripleRow 86 22 1 90 34 0 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row87 : TripleComponentParentRow :=
  tripleRow 87 23 1 90 35 0 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row88 : TripleComponentParentRow :=
  tripleRow 88 24 1 91 24 0 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row89 : TripleComponentParentRow :=
  tripleRow 89 25 1 91 25 0 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row90 : TripleComponentParentRow :=
  tripleRow 90 26 1 91 26 0 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row91 : TripleComponentParentRow :=
  tripleRow 91 27 1 91 27 0 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row92 : TripleComponentParentRow :=
  tripleRow 92 28 1 91 40 0 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row93 : TripleComponentParentRow :=
  tripleRow 93 29 1 91 41 0 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row94 : TripleComponentParentRow :=
  tripleRow 94 30 1 91 42 0 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row95 : TripleComponentParentRow :=
  tripleRow 95 31 1 91 43 0 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row80
  , tttLargeFiber30Row81
  , tttLargeFiber30Row82
  , tttLargeFiber30Row83
  , tttLargeFiber30Row84
  , tttLargeFiber30Row85
  , tttLargeFiber30Row86
  , tttLargeFiber30Row87
  , tttLargeFiber30Row88
  , tttLargeFiber30Row89
  , tttLargeFiber30Row90
  , tttLargeFiber30Row91
  , tttLargeFiber30Row92
  , tttLargeFiber30Row93
  , tttLargeFiber30Row94
  , tttLargeFiber30Row95
  ]

def tttLargeFiber30Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber30Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber30Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber30Block1Chunk1Sources

theorem tttLargeFiber30Block1Chunk1SourcesCheck_ok :
    tttLargeFiber30Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber30Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block1Chunk1RowValid
    (listGetD tttLargeFiber30Block1Chunk1Rows i default)

def tttLargeFiber30Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block1Chunk1Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block1Chunk1Sources 0 0 == 80
      && tttLargeFiber30ParentOf 80 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block1Chunk1Sources 1 0 == 81
      && tttLargeFiber30ParentOf 81 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block1Chunk1Sources 2 0 == 82
      && tttLargeFiber30ParentOf 82 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block1Chunk1Sources 3 0 == 83
      && tttLargeFiber30ParentOf 83 == 19
      && tttLargeFiber30ParentOf 19 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block1Chunk1Sources 4 0 == 84
      && tttLargeFiber30ParentOf 84 == 20
      && tttLargeFiber30ParentOf 20 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block1Chunk1Sources 5 0 == 85
      && tttLargeFiber30ParentOf 85 == 21
      && tttLargeFiber30ParentOf 21 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block1Chunk1Sources 6 0 == 86
      && tttLargeFiber30ParentOf 86 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block1Chunk1Sources 7 0 == 87
      && tttLargeFiber30ParentOf 87 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block1Chunk1Sources 8 0 == 88
      && tttLargeFiber30ParentOf 88 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block1Chunk1Sources 9 0 == 89
      && tttLargeFiber30ParentOf 89 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block1Chunk1Sources 10 0 == 90
      && tttLargeFiber30ParentOf 90 == 26
      && tttLargeFiber30ParentOf 26 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block1Chunk1Sources 11 0 == 91
      && tttLargeFiber30ParentOf 91 == 27
      && tttLargeFiber30ParentOf 27 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block1Chunk1Sources 12 0 == 92
      && tttLargeFiber30ParentOf 92 == 28
      && tttLargeFiber30ParentOf 28 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block1Chunk1Sources 13 0 == 93
      && tttLargeFiber30ParentOf 93 == 29
      && tttLargeFiber30ParentOf 29 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block1Chunk1Sources 14 0 == 94
      && tttLargeFiber30ParentOf 94 == 30
      && tttLargeFiber30ParentOf 30 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block1Chunk1Sources 15 0 == 95
      && tttLargeFiber30ParentOf 95 == 31
      && tttLargeFiber30ParentOf 31 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block1Chunk1Row_0_ok :
    tttLargeFiber30Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_1_ok :
    tttLargeFiber30Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_2_ok :
    tttLargeFiber30Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_3_ok :
    tttLargeFiber30Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_4_ok :
    tttLargeFiber30Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_5_ok :
    tttLargeFiber30Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_6_ok :
    tttLargeFiber30Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_7_ok :
    tttLargeFiber30Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_8_ok :
    tttLargeFiber30Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_9_ok :
    tttLargeFiber30Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_10_ok :
    tttLargeFiber30Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_11_ok :
    tttLargeFiber30Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_12_ok :
    tttLargeFiber30Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_13_ok :
    tttLargeFiber30Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_14_ok :
    tttLargeFiber30Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1Row_15_ok :
    tttLargeFiber30Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_0_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_1_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_2_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_3_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_4_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_5_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_6_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_7_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_8_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_9_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_10_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_11_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_12_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_13_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_14_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentMap_15_ok :
    tttLargeFiber30Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_0_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_1_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_2_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_3_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_4_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_5_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_6_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_7_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_8_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_9_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_10_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_11_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_12_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_13_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_14_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk1ParentPath_15_ok :
    tttLargeFiber30Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber30Block1Chunk1RowCheck 0
    && tttLargeFiber30Block1Chunk1RowCheck 1
    && tttLargeFiber30Block1Chunk1RowCheck 2
    && tttLargeFiber30Block1Chunk1RowCheck 3
    && tttLargeFiber30Block1Chunk1RowCheck 4
    && tttLargeFiber30Block1Chunk1RowCheck 5
    && tttLargeFiber30Block1Chunk1RowCheck 6
    && tttLargeFiber30Block1Chunk1RowCheck 7
    && tttLargeFiber30Block1Chunk1RowCheck 8
    && tttLargeFiber30Block1Chunk1RowCheck 9
    && tttLargeFiber30Block1Chunk1RowCheck 10
    && tttLargeFiber30Block1Chunk1RowCheck 11
    && tttLargeFiber30Block1Chunk1RowCheck 12
    && tttLargeFiber30Block1Chunk1RowCheck 13
    && tttLargeFiber30Block1Chunk1RowCheck 14
    && tttLargeFiber30Block1Chunk1RowCheck 15

theorem tttLargeFiber30Block1Chunk1RowsAudit_ok :
    tttLargeFiber30Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber30Block1Chunk1RowsAudit,
    tttLargeFiber30Block1Chunk1Row_0_ok,
    tttLargeFiber30Block1Chunk1Row_1_ok,
    tttLargeFiber30Block1Chunk1Row_2_ok,
    tttLargeFiber30Block1Chunk1Row_3_ok,
    tttLargeFiber30Block1Chunk1Row_4_ok,
    tttLargeFiber30Block1Chunk1Row_5_ok,
    tttLargeFiber30Block1Chunk1Row_6_ok,
    tttLargeFiber30Block1Chunk1Row_7_ok,
    tttLargeFiber30Block1Chunk1Row_8_ok,
    tttLargeFiber30Block1Chunk1Row_9_ok,
    tttLargeFiber30Block1Chunk1Row_10_ok,
    tttLargeFiber30Block1Chunk1Row_11_ok,
    tttLargeFiber30Block1Chunk1Row_12_ok,
    tttLargeFiber30Block1Chunk1Row_13_ok,
    tttLargeFiber30Block1Chunk1Row_14_ok,
    tttLargeFiber30Block1Chunk1Row_15_ok]

def tttLargeFiber30Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber30Block1Chunk1ParentMapCheck 0
    && tttLargeFiber30Block1Chunk1ParentMapCheck 1
    && tttLargeFiber30Block1Chunk1ParentMapCheck 2
    && tttLargeFiber30Block1Chunk1ParentMapCheck 3
    && tttLargeFiber30Block1Chunk1ParentMapCheck 4
    && tttLargeFiber30Block1Chunk1ParentMapCheck 5
    && tttLargeFiber30Block1Chunk1ParentMapCheck 6
    && tttLargeFiber30Block1Chunk1ParentMapCheck 7
    && tttLargeFiber30Block1Chunk1ParentMapCheck 8
    && tttLargeFiber30Block1Chunk1ParentMapCheck 9
    && tttLargeFiber30Block1Chunk1ParentMapCheck 10
    && tttLargeFiber30Block1Chunk1ParentMapCheck 11
    && tttLargeFiber30Block1Chunk1ParentMapCheck 12
    && tttLargeFiber30Block1Chunk1ParentMapCheck 13
    && tttLargeFiber30Block1Chunk1ParentMapCheck 14
    && tttLargeFiber30Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber30Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber30Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber30Block1Chunk1ParentMapAudit,
    tttLargeFiber30Block1Chunk1ParentMap_0_ok,
    tttLargeFiber30Block1Chunk1ParentMap_1_ok,
    tttLargeFiber30Block1Chunk1ParentMap_2_ok,
    tttLargeFiber30Block1Chunk1ParentMap_3_ok,
    tttLargeFiber30Block1Chunk1ParentMap_4_ok,
    tttLargeFiber30Block1Chunk1ParentMap_5_ok,
    tttLargeFiber30Block1Chunk1ParentMap_6_ok,
    tttLargeFiber30Block1Chunk1ParentMap_7_ok,
    tttLargeFiber30Block1Chunk1ParentMap_8_ok,
    tttLargeFiber30Block1Chunk1ParentMap_9_ok,
    tttLargeFiber30Block1Chunk1ParentMap_10_ok,
    tttLargeFiber30Block1Chunk1ParentMap_11_ok,
    tttLargeFiber30Block1Chunk1ParentMap_12_ok,
    tttLargeFiber30Block1Chunk1ParentMap_13_ok,
    tttLargeFiber30Block1Chunk1ParentMap_14_ok,
    tttLargeFiber30Block1Chunk1ParentMap_15_ok]

def tttLargeFiber30Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber30Block1Chunk1ParentPathCheck 0
    && tttLargeFiber30Block1Chunk1ParentPathCheck 1
    && tttLargeFiber30Block1Chunk1ParentPathCheck 2
    && tttLargeFiber30Block1Chunk1ParentPathCheck 3
    && tttLargeFiber30Block1Chunk1ParentPathCheck 4
    && tttLargeFiber30Block1Chunk1ParentPathCheck 5
    && tttLargeFiber30Block1Chunk1ParentPathCheck 6
    && tttLargeFiber30Block1Chunk1ParentPathCheck 7
    && tttLargeFiber30Block1Chunk1ParentPathCheck 8
    && tttLargeFiber30Block1Chunk1ParentPathCheck 9
    && tttLargeFiber30Block1Chunk1ParentPathCheck 10
    && tttLargeFiber30Block1Chunk1ParentPathCheck 11
    && tttLargeFiber30Block1Chunk1ParentPathCheck 12
    && tttLargeFiber30Block1Chunk1ParentPathCheck 13
    && tttLargeFiber30Block1Chunk1ParentPathCheck 14
    && tttLargeFiber30Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber30Block1Chunk1ParentsAudit_ok :
    tttLargeFiber30Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber30Block1Chunk1ParentsAudit,
    tttLargeFiber30Block1Chunk1ParentPath_0_ok,
    tttLargeFiber30Block1Chunk1ParentPath_1_ok,
    tttLargeFiber30Block1Chunk1ParentPath_2_ok,
    tttLargeFiber30Block1Chunk1ParentPath_3_ok,
    tttLargeFiber30Block1Chunk1ParentPath_4_ok,
    tttLargeFiber30Block1Chunk1ParentPath_5_ok,
    tttLargeFiber30Block1Chunk1ParentPath_6_ok,
    tttLargeFiber30Block1Chunk1ParentPath_7_ok,
    tttLargeFiber30Block1Chunk1ParentPath_8_ok,
    tttLargeFiber30Block1Chunk1ParentPath_9_ok,
    tttLargeFiber30Block1Chunk1ParentPath_10_ok,
    tttLargeFiber30Block1Chunk1ParentPath_11_ok,
    tttLargeFiber30Block1Chunk1ParentPath_12_ok,
    tttLargeFiber30Block1Chunk1ParentPath_13_ok,
    tttLargeFiber30Block1Chunk1ParentPath_14_ok,
    tttLargeFiber30Block1Chunk1ParentPath_15_ok]

def tttLargeFiber30Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block1Chunk1SourcesCheck &&
    tttLargeFiber30Block1Chunk1RowsAudit &&
    tttLargeFiber30Block1Chunk1ParentMapAudit &&
    tttLargeFiber30Block1Chunk1ParentsAudit

theorem tttLargeFiber30Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber30Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block1Chunk1SourcesCheck_ok,
    tttLargeFiber30Block1Chunk1RowsAudit_ok,
    tttLargeFiber30Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber30Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
