import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block0Chunk1Sources : List Nat :=
  [   16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 30, 31]

def tttLargeFiber30Row16 : TripleComponentParentRow :=
  tripleRow 16 0 0 82 16 0 80 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row17 : TripleComponentParentRow :=
  tripleRow 17 1 0 82 17 0 80 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row18 : TripleComponentParentRow :=
  tripleRow 18 2 0 82 18 0 80 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row19 : TripleComponentParentRow :=
  tripleRow 19 3 0 82 19 0 80 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row20 : TripleComponentParentRow :=
  tripleRow 20 16 0 82 32 0 82 16
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row21 : TripleComponentParentRow :=
  tripleRow 21 17 0 82 33 0 82 17
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row22 : TripleComponentParentRow :=
  tripleRow 22 6 0 82 34 0 80 102
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row23 : TripleComponentParentRow :=
  tripleRow 23 7 0 82 35 0 80 103
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row24 : TripleComponentParentRow :=
  tripleRow 24 8 0 83 24 0 81 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row25 : TripleComponentParentRow :=
  tripleRow 25 9 0 83 25 0 81 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row26 : TripleComponentParentRow :=
  tripleRow 26 10 0 83 26 0 81 90
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row27 : TripleComponentParentRow :=
  tripleRow 27 11 0 83 27 0 81 91
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row28 : TripleComponentParentRow :=
  tripleRow 28 24 0 83 40 0 83 24
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row29 : TripleComponentParentRow :=
  tripleRow 29 25 0 83 41 0 83 25
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row30 : TripleComponentParentRow :=
  tripleRow 30 14 0 83 42 0 81 110
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row31 : TripleComponentParentRow :=
  tripleRow 31 15 0 83 43 0 81 111
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row16
  , tttLargeFiber30Row17
  , tttLargeFiber30Row18
  , tttLargeFiber30Row19
  , tttLargeFiber30Row20
  , tttLargeFiber30Row21
  , tttLargeFiber30Row22
  , tttLargeFiber30Row23
  , tttLargeFiber30Row24
  , tttLargeFiber30Row25
  , tttLargeFiber30Row26
  , tttLargeFiber30Row27
  , tttLargeFiber30Row28
  , tttLargeFiber30Row29
  , tttLargeFiber30Row30
  , tttLargeFiber30Row31
  ]

def tttLargeFiber30Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber30Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber30Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber30Block0Chunk1Sources

theorem tttLargeFiber30Block0Chunk1SourcesCheck_ok :
    tttLargeFiber30Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber30Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block0Chunk1RowValid
    (listGetD tttLargeFiber30Block0Chunk1Rows i default)

def tttLargeFiber30Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block0Chunk1Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block0Chunk1Sources 0 0 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block0Chunk1Sources 1 0 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block0Chunk1Sources 2 0 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block0Chunk1Sources 3 0 == 19
      && tttLargeFiber30ParentOf 19 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block0Chunk1Sources 4 0 == 20
      && tttLargeFiber30ParentOf 20 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block0Chunk1Sources 5 0 == 21
      && tttLargeFiber30ParentOf 21 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block0Chunk1Sources 6 0 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block0Chunk1Sources 7 0 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block0Chunk1Sources 8 0 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block0Chunk1Sources 9 0 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block0Chunk1Sources 10 0 == 26
      && tttLargeFiber30ParentOf 26 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block0Chunk1Sources 11 0 == 27
      && tttLargeFiber30ParentOf 27 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block0Chunk1Sources 12 0 == 28
      && tttLargeFiber30ParentOf 28 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block0Chunk1Sources 13 0 == 29
      && tttLargeFiber30ParentOf 29 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block0Chunk1Sources 14 0 == 30
      && tttLargeFiber30ParentOf 30 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block0Chunk1Sources 15 0 == 31
      && tttLargeFiber30ParentOf 31 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block0Chunk1Row_0_ok :
    tttLargeFiber30Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_1_ok :
    tttLargeFiber30Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_2_ok :
    tttLargeFiber30Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_3_ok :
    tttLargeFiber30Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_4_ok :
    tttLargeFiber30Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_5_ok :
    tttLargeFiber30Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_6_ok :
    tttLargeFiber30Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_7_ok :
    tttLargeFiber30Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_8_ok :
    tttLargeFiber30Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_9_ok :
    tttLargeFiber30Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_10_ok :
    tttLargeFiber30Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_11_ok :
    tttLargeFiber30Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_12_ok :
    tttLargeFiber30Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_13_ok :
    tttLargeFiber30Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_14_ok :
    tttLargeFiber30Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1Row_15_ok :
    tttLargeFiber30Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_0_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_1_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_2_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_3_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_4_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_5_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_6_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_7_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_8_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_9_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_10_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_11_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_12_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_13_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_14_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentMap_15_ok :
    tttLargeFiber30Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_0_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_1_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_2_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_3_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_4_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_5_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_6_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_7_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_8_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_9_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_10_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_11_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_12_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_13_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_14_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk1ParentPath_15_ok :
    tttLargeFiber30Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber30Block0Chunk1RowCheck 0
    && tttLargeFiber30Block0Chunk1RowCheck 1
    && tttLargeFiber30Block0Chunk1RowCheck 2
    && tttLargeFiber30Block0Chunk1RowCheck 3
    && tttLargeFiber30Block0Chunk1RowCheck 4
    && tttLargeFiber30Block0Chunk1RowCheck 5
    && tttLargeFiber30Block0Chunk1RowCheck 6
    && tttLargeFiber30Block0Chunk1RowCheck 7
    && tttLargeFiber30Block0Chunk1RowCheck 8
    && tttLargeFiber30Block0Chunk1RowCheck 9
    && tttLargeFiber30Block0Chunk1RowCheck 10
    && tttLargeFiber30Block0Chunk1RowCheck 11
    && tttLargeFiber30Block0Chunk1RowCheck 12
    && tttLargeFiber30Block0Chunk1RowCheck 13
    && tttLargeFiber30Block0Chunk1RowCheck 14
    && tttLargeFiber30Block0Chunk1RowCheck 15

theorem tttLargeFiber30Block0Chunk1RowsAudit_ok :
    tttLargeFiber30Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber30Block0Chunk1RowsAudit,
    tttLargeFiber30Block0Chunk1Row_0_ok,
    tttLargeFiber30Block0Chunk1Row_1_ok,
    tttLargeFiber30Block0Chunk1Row_2_ok,
    tttLargeFiber30Block0Chunk1Row_3_ok,
    tttLargeFiber30Block0Chunk1Row_4_ok,
    tttLargeFiber30Block0Chunk1Row_5_ok,
    tttLargeFiber30Block0Chunk1Row_6_ok,
    tttLargeFiber30Block0Chunk1Row_7_ok,
    tttLargeFiber30Block0Chunk1Row_8_ok,
    tttLargeFiber30Block0Chunk1Row_9_ok,
    tttLargeFiber30Block0Chunk1Row_10_ok,
    tttLargeFiber30Block0Chunk1Row_11_ok,
    tttLargeFiber30Block0Chunk1Row_12_ok,
    tttLargeFiber30Block0Chunk1Row_13_ok,
    tttLargeFiber30Block0Chunk1Row_14_ok,
    tttLargeFiber30Block0Chunk1Row_15_ok]

def tttLargeFiber30Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber30Block0Chunk1ParentMapCheck 0
    && tttLargeFiber30Block0Chunk1ParentMapCheck 1
    && tttLargeFiber30Block0Chunk1ParentMapCheck 2
    && tttLargeFiber30Block0Chunk1ParentMapCheck 3
    && tttLargeFiber30Block0Chunk1ParentMapCheck 4
    && tttLargeFiber30Block0Chunk1ParentMapCheck 5
    && tttLargeFiber30Block0Chunk1ParentMapCheck 6
    && tttLargeFiber30Block0Chunk1ParentMapCheck 7
    && tttLargeFiber30Block0Chunk1ParentMapCheck 8
    && tttLargeFiber30Block0Chunk1ParentMapCheck 9
    && tttLargeFiber30Block0Chunk1ParentMapCheck 10
    && tttLargeFiber30Block0Chunk1ParentMapCheck 11
    && tttLargeFiber30Block0Chunk1ParentMapCheck 12
    && tttLargeFiber30Block0Chunk1ParentMapCheck 13
    && tttLargeFiber30Block0Chunk1ParentMapCheck 14
    && tttLargeFiber30Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber30Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber30Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber30Block0Chunk1ParentMapAudit,
    tttLargeFiber30Block0Chunk1ParentMap_0_ok,
    tttLargeFiber30Block0Chunk1ParentMap_1_ok,
    tttLargeFiber30Block0Chunk1ParentMap_2_ok,
    tttLargeFiber30Block0Chunk1ParentMap_3_ok,
    tttLargeFiber30Block0Chunk1ParentMap_4_ok,
    tttLargeFiber30Block0Chunk1ParentMap_5_ok,
    tttLargeFiber30Block0Chunk1ParentMap_6_ok,
    tttLargeFiber30Block0Chunk1ParentMap_7_ok,
    tttLargeFiber30Block0Chunk1ParentMap_8_ok,
    tttLargeFiber30Block0Chunk1ParentMap_9_ok,
    tttLargeFiber30Block0Chunk1ParentMap_10_ok,
    tttLargeFiber30Block0Chunk1ParentMap_11_ok,
    tttLargeFiber30Block0Chunk1ParentMap_12_ok,
    tttLargeFiber30Block0Chunk1ParentMap_13_ok,
    tttLargeFiber30Block0Chunk1ParentMap_14_ok,
    tttLargeFiber30Block0Chunk1ParentMap_15_ok]

def tttLargeFiber30Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber30Block0Chunk1ParentPathCheck 0
    && tttLargeFiber30Block0Chunk1ParentPathCheck 1
    && tttLargeFiber30Block0Chunk1ParentPathCheck 2
    && tttLargeFiber30Block0Chunk1ParentPathCheck 3
    && tttLargeFiber30Block0Chunk1ParentPathCheck 4
    && tttLargeFiber30Block0Chunk1ParentPathCheck 5
    && tttLargeFiber30Block0Chunk1ParentPathCheck 6
    && tttLargeFiber30Block0Chunk1ParentPathCheck 7
    && tttLargeFiber30Block0Chunk1ParentPathCheck 8
    && tttLargeFiber30Block0Chunk1ParentPathCheck 9
    && tttLargeFiber30Block0Chunk1ParentPathCheck 10
    && tttLargeFiber30Block0Chunk1ParentPathCheck 11
    && tttLargeFiber30Block0Chunk1ParentPathCheck 12
    && tttLargeFiber30Block0Chunk1ParentPathCheck 13
    && tttLargeFiber30Block0Chunk1ParentPathCheck 14
    && tttLargeFiber30Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber30Block0Chunk1ParentsAudit_ok :
    tttLargeFiber30Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber30Block0Chunk1ParentsAudit,
    tttLargeFiber30Block0Chunk1ParentPath_0_ok,
    tttLargeFiber30Block0Chunk1ParentPath_1_ok,
    tttLargeFiber30Block0Chunk1ParentPath_2_ok,
    tttLargeFiber30Block0Chunk1ParentPath_3_ok,
    tttLargeFiber30Block0Chunk1ParentPath_4_ok,
    tttLargeFiber30Block0Chunk1ParentPath_5_ok,
    tttLargeFiber30Block0Chunk1ParentPath_6_ok,
    tttLargeFiber30Block0Chunk1ParentPath_7_ok,
    tttLargeFiber30Block0Chunk1ParentPath_8_ok,
    tttLargeFiber30Block0Chunk1ParentPath_9_ok,
    tttLargeFiber30Block0Chunk1ParentPath_10_ok,
    tttLargeFiber30Block0Chunk1ParentPath_11_ok,
    tttLargeFiber30Block0Chunk1ParentPath_12_ok,
    tttLargeFiber30Block0Chunk1ParentPath_13_ok,
    tttLargeFiber30Block0Chunk1ParentPath_14_ok,
    tttLargeFiber30Block0Chunk1ParentPath_15_ok]

def tttLargeFiber30Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block0Chunk1SourcesCheck &&
    tttLargeFiber30Block0Chunk1RowsAudit &&
    tttLargeFiber30Block0Chunk1ParentMapAudit &&
    tttLargeFiber30Block0Chunk1ParentsAudit

theorem tttLargeFiber30Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber30Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block0Chunk1SourcesCheck_ok,
    tttLargeFiber30Block0Chunk1RowsAudit_ok,
    tttLargeFiber30Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber30Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
