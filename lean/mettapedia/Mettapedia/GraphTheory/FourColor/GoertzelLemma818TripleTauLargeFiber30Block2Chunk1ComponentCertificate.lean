import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 2 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block2Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block2Chunk1Sources : List Nat :=
  [   144, 145, 146, 147, 148, 149, 150, 151,
   152, 153, 154, 155, 156, 157, 158, 159]

def tttLargeFiber30Row144 : TripleComponentParentRow :=
  tripleRow 144 16 2 18 16 0 82 16
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row145 : TripleComponentParentRow :=
  tripleRow 145 17 2 18 17 0 82 17
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row146 : TripleComponentParentRow :=
  tripleRow 146 18 2 18 18 0 82 18
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row147 : TripleComponentParentRow :=
  tripleRow 147 19 2 18 19 0 82 19
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row148 : TripleComponentParentRow :=
  tripleRow 148 20 2 18 32 0 82 32
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row149 : TripleComponentParentRow :=
  tripleRow 149 21 2 18 33 0 82 33
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row150 : TripleComponentParentRow :=
  tripleRow 150 22 2 18 34 0 82 34
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row151 : TripleComponentParentRow :=
  tripleRow 151 23 2 18 35 0 82 35
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row152 : TripleComponentParentRow :=
  tripleRow 152 24 2 19 24 0 83 24
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row153 : TripleComponentParentRow :=
  tripleRow 153 25 2 19 25 0 83 25
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row154 : TripleComponentParentRow :=
  tripleRow 154 26 2 19 26 0 83 26
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row155 : TripleComponentParentRow :=
  tripleRow 155 27 2 19 27 0 83 27
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row156 : TripleComponentParentRow :=
  tripleRow 156 28 2 19 40 0 83 40
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row157 : TripleComponentParentRow :=
  tripleRow 157 29 2 19 41 0 83 41
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row158 : TripleComponentParentRow :=
  tripleRow 158 30 2 19 42 0 83 42
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row159 : TripleComponentParentRow :=
  tripleRow 159 31 2 19 43 0 83 43
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Block2Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row144
  , tttLargeFiber30Row145
  , tttLargeFiber30Row146
  , tttLargeFiber30Row147
  , tttLargeFiber30Row148
  , tttLargeFiber30Row149
  , tttLargeFiber30Row150
  , tttLargeFiber30Row151
  , tttLargeFiber30Row152
  , tttLargeFiber30Row153
  , tttLargeFiber30Row154
  , tttLargeFiber30Row155
  , tttLargeFiber30Row156
  , tttLargeFiber30Row157
  , tttLargeFiber30Row158
  , tttLargeFiber30Row159
  ]

def tttLargeFiber30Block2Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block2Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block2Chunk1ExpectedContains row.source &&
    tttLargeFiber30Block2Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block2Chunk1SourcesCheck : Bool :=
  (tttLargeFiber30Block2Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber30Block2Chunk1Sources

theorem tttLargeFiber30Block2Chunk1SourcesCheck_ok :
    tttLargeFiber30Block2Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber30Block2Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block2Chunk1RowValid
    (listGetD tttLargeFiber30Block2Chunk1Rows i default)

def tttLargeFiber30Block2Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block2Chunk1Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block2Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block2Chunk1Sources 0 0 == 144
      && tttLargeFiber30ParentOf 144 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block2Chunk1Sources 1 0 == 145
      && tttLargeFiber30ParentOf 145 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block2Chunk1Sources 2 0 == 146
      && tttLargeFiber30ParentOf 146 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block2Chunk1Sources 3 0 == 147
      && tttLargeFiber30ParentOf 147 == 19
      && tttLargeFiber30ParentOf 19 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block2Chunk1Sources 4 0 == 148
      && tttLargeFiber30ParentOf 148 == 20
      && tttLargeFiber30ParentOf 20 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block2Chunk1Sources 5 0 == 149
      && tttLargeFiber30ParentOf 149 == 21
      && tttLargeFiber30ParentOf 21 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block2Chunk1Sources 6 0 == 150
      && tttLargeFiber30ParentOf 150 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block2Chunk1Sources 7 0 == 151
      && tttLargeFiber30ParentOf 151 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block2Chunk1Sources 8 0 == 152
      && tttLargeFiber30ParentOf 152 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block2Chunk1Sources 9 0 == 153
      && tttLargeFiber30ParentOf 153 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block2Chunk1Sources 10 0 == 154
      && tttLargeFiber30ParentOf 154 == 26
      && tttLargeFiber30ParentOf 26 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block2Chunk1Sources 11 0 == 155
      && tttLargeFiber30ParentOf 155 == 27
      && tttLargeFiber30ParentOf 27 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block2Chunk1Sources 12 0 == 156
      && tttLargeFiber30ParentOf 156 == 28
      && tttLargeFiber30ParentOf 28 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block2Chunk1Sources 13 0 == 157
      && tttLargeFiber30ParentOf 157 == 29
      && tttLargeFiber30ParentOf 29 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block2Chunk1Sources 14 0 == 158
      && tttLargeFiber30ParentOf 158 == 30
      && tttLargeFiber30ParentOf 30 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block2Chunk1Sources 15 0 == 159
      && tttLargeFiber30ParentOf 159 == 31
      && tttLargeFiber30ParentOf 31 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block2Chunk1Row_0_ok :
    tttLargeFiber30Block2Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_1_ok :
    tttLargeFiber30Block2Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_2_ok :
    tttLargeFiber30Block2Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_3_ok :
    tttLargeFiber30Block2Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_4_ok :
    tttLargeFiber30Block2Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_5_ok :
    tttLargeFiber30Block2Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_6_ok :
    tttLargeFiber30Block2Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_7_ok :
    tttLargeFiber30Block2Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_8_ok :
    tttLargeFiber30Block2Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_9_ok :
    tttLargeFiber30Block2Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_10_ok :
    tttLargeFiber30Block2Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_11_ok :
    tttLargeFiber30Block2Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_12_ok :
    tttLargeFiber30Block2Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_13_ok :
    tttLargeFiber30Block2Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_14_ok :
    tttLargeFiber30Block2Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1Row_15_ok :
    tttLargeFiber30Block2Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_0_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_1_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_2_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_3_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_4_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_5_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_6_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_7_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_8_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_9_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_10_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_11_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_12_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_13_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_14_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentMap_15_ok :
    tttLargeFiber30Block2Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_0_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_1_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_2_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_3_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_4_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_5_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_6_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_7_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_8_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_9_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_10_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_11_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_12_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_13_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_14_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk1ParentPath_15_ok :
    tttLargeFiber30Block2Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block2Chunk1RowsAudit : Bool :=
  tttLargeFiber30Block2Chunk1RowCheck 0
    && tttLargeFiber30Block2Chunk1RowCheck 1
    && tttLargeFiber30Block2Chunk1RowCheck 2
    && tttLargeFiber30Block2Chunk1RowCheck 3
    && tttLargeFiber30Block2Chunk1RowCheck 4
    && tttLargeFiber30Block2Chunk1RowCheck 5
    && tttLargeFiber30Block2Chunk1RowCheck 6
    && tttLargeFiber30Block2Chunk1RowCheck 7
    && tttLargeFiber30Block2Chunk1RowCheck 8
    && tttLargeFiber30Block2Chunk1RowCheck 9
    && tttLargeFiber30Block2Chunk1RowCheck 10
    && tttLargeFiber30Block2Chunk1RowCheck 11
    && tttLargeFiber30Block2Chunk1RowCheck 12
    && tttLargeFiber30Block2Chunk1RowCheck 13
    && tttLargeFiber30Block2Chunk1RowCheck 14
    && tttLargeFiber30Block2Chunk1RowCheck 15

theorem tttLargeFiber30Block2Chunk1RowsAudit_ok :
    tttLargeFiber30Block2Chunk1RowsAudit = true := by
  simp [tttLargeFiber30Block2Chunk1RowsAudit,
    tttLargeFiber30Block2Chunk1Row_0_ok,
    tttLargeFiber30Block2Chunk1Row_1_ok,
    tttLargeFiber30Block2Chunk1Row_2_ok,
    tttLargeFiber30Block2Chunk1Row_3_ok,
    tttLargeFiber30Block2Chunk1Row_4_ok,
    tttLargeFiber30Block2Chunk1Row_5_ok,
    tttLargeFiber30Block2Chunk1Row_6_ok,
    tttLargeFiber30Block2Chunk1Row_7_ok,
    tttLargeFiber30Block2Chunk1Row_8_ok,
    tttLargeFiber30Block2Chunk1Row_9_ok,
    tttLargeFiber30Block2Chunk1Row_10_ok,
    tttLargeFiber30Block2Chunk1Row_11_ok,
    tttLargeFiber30Block2Chunk1Row_12_ok,
    tttLargeFiber30Block2Chunk1Row_13_ok,
    tttLargeFiber30Block2Chunk1Row_14_ok,
    tttLargeFiber30Block2Chunk1Row_15_ok]

def tttLargeFiber30Block2Chunk1ParentMapAudit : Bool :=
  tttLargeFiber30Block2Chunk1ParentMapCheck 0
    && tttLargeFiber30Block2Chunk1ParentMapCheck 1
    && tttLargeFiber30Block2Chunk1ParentMapCheck 2
    && tttLargeFiber30Block2Chunk1ParentMapCheck 3
    && tttLargeFiber30Block2Chunk1ParentMapCheck 4
    && tttLargeFiber30Block2Chunk1ParentMapCheck 5
    && tttLargeFiber30Block2Chunk1ParentMapCheck 6
    && tttLargeFiber30Block2Chunk1ParentMapCheck 7
    && tttLargeFiber30Block2Chunk1ParentMapCheck 8
    && tttLargeFiber30Block2Chunk1ParentMapCheck 9
    && tttLargeFiber30Block2Chunk1ParentMapCheck 10
    && tttLargeFiber30Block2Chunk1ParentMapCheck 11
    && tttLargeFiber30Block2Chunk1ParentMapCheck 12
    && tttLargeFiber30Block2Chunk1ParentMapCheck 13
    && tttLargeFiber30Block2Chunk1ParentMapCheck 14
    && tttLargeFiber30Block2Chunk1ParentMapCheck 15

theorem tttLargeFiber30Block2Chunk1ParentMapAudit_ok :
    tttLargeFiber30Block2Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber30Block2Chunk1ParentMapAudit,
    tttLargeFiber30Block2Chunk1ParentMap_0_ok,
    tttLargeFiber30Block2Chunk1ParentMap_1_ok,
    tttLargeFiber30Block2Chunk1ParentMap_2_ok,
    tttLargeFiber30Block2Chunk1ParentMap_3_ok,
    tttLargeFiber30Block2Chunk1ParentMap_4_ok,
    tttLargeFiber30Block2Chunk1ParentMap_5_ok,
    tttLargeFiber30Block2Chunk1ParentMap_6_ok,
    tttLargeFiber30Block2Chunk1ParentMap_7_ok,
    tttLargeFiber30Block2Chunk1ParentMap_8_ok,
    tttLargeFiber30Block2Chunk1ParentMap_9_ok,
    tttLargeFiber30Block2Chunk1ParentMap_10_ok,
    tttLargeFiber30Block2Chunk1ParentMap_11_ok,
    tttLargeFiber30Block2Chunk1ParentMap_12_ok,
    tttLargeFiber30Block2Chunk1ParentMap_13_ok,
    tttLargeFiber30Block2Chunk1ParentMap_14_ok,
    tttLargeFiber30Block2Chunk1ParentMap_15_ok]

def tttLargeFiber30Block2Chunk1ParentsAudit : Bool :=
  tttLargeFiber30Block2Chunk1ParentPathCheck 0
    && tttLargeFiber30Block2Chunk1ParentPathCheck 1
    && tttLargeFiber30Block2Chunk1ParentPathCheck 2
    && tttLargeFiber30Block2Chunk1ParentPathCheck 3
    && tttLargeFiber30Block2Chunk1ParentPathCheck 4
    && tttLargeFiber30Block2Chunk1ParentPathCheck 5
    && tttLargeFiber30Block2Chunk1ParentPathCheck 6
    && tttLargeFiber30Block2Chunk1ParentPathCheck 7
    && tttLargeFiber30Block2Chunk1ParentPathCheck 8
    && tttLargeFiber30Block2Chunk1ParentPathCheck 9
    && tttLargeFiber30Block2Chunk1ParentPathCheck 10
    && tttLargeFiber30Block2Chunk1ParentPathCheck 11
    && tttLargeFiber30Block2Chunk1ParentPathCheck 12
    && tttLargeFiber30Block2Chunk1ParentPathCheck 13
    && tttLargeFiber30Block2Chunk1ParentPathCheck 14
    && tttLargeFiber30Block2Chunk1ParentPathCheck 15

theorem tttLargeFiber30Block2Chunk1ParentsAudit_ok :
    tttLargeFiber30Block2Chunk1ParentsAudit = true := by
  simp [tttLargeFiber30Block2Chunk1ParentsAudit,
    tttLargeFiber30Block2Chunk1ParentPath_0_ok,
    tttLargeFiber30Block2Chunk1ParentPath_1_ok,
    tttLargeFiber30Block2Chunk1ParentPath_2_ok,
    tttLargeFiber30Block2Chunk1ParentPath_3_ok,
    tttLargeFiber30Block2Chunk1ParentPath_4_ok,
    tttLargeFiber30Block2Chunk1ParentPath_5_ok,
    tttLargeFiber30Block2Chunk1ParentPath_6_ok,
    tttLargeFiber30Block2Chunk1ParentPath_7_ok,
    tttLargeFiber30Block2Chunk1ParentPath_8_ok,
    tttLargeFiber30Block2Chunk1ParentPath_9_ok,
    tttLargeFiber30Block2Chunk1ParentPath_10_ok,
    tttLargeFiber30Block2Chunk1ParentPath_11_ok,
    tttLargeFiber30Block2Chunk1ParentPath_12_ok,
    tttLargeFiber30Block2Chunk1ParentPath_13_ok,
    tttLargeFiber30Block2Chunk1ParentPath_14_ok,
    tttLargeFiber30Block2Chunk1ParentPath_15_ok]

def tttLargeFiber30Block2Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block2Chunk1SourcesCheck &&
    tttLargeFiber30Block2Chunk1RowsAudit &&
    tttLargeFiber30Block2Chunk1ParentMapAudit &&
    tttLargeFiber30Block2Chunk1ParentsAudit

theorem tttLargeFiber30Block2Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber30Block2Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block2Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block2Chunk1SourcesCheck_ok,
    tttLargeFiber30Block2Chunk1RowsAudit_ok,
    tttLargeFiber30Block2Chunk1ParentMapAudit_ok,
    tttLargeFiber30Block2Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block2Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
