import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 0 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block0Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block0Chunk2Sources : List Nat :=
  [   32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47]

def tttLargeFiber30Row32 : TripleComponentParentRow :=
  tripleRow 32 48 0 100 132 0 102 64
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row33 : TripleComponentParentRow :=
  tripleRow 33 49 0 100 133 0 102 65
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row34 : TripleComponentParentRow :=
  tripleRow 34 22 0 100 134 0 82 34
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row35 : TripleComponentParentRow :=
  tripleRow 35 23 0 100 135 0 82 35
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row36 : TripleComponentParentRow :=
  tripleRow 36 18 0 100 180 0 82 18
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row37 : TripleComponentParentRow :=
  tripleRow 37 39 0 100 181 0 100 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row38 : TripleComponentParentRow :=
  tripleRow 38 17 0 100 182 0 82 17
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row39 : TripleComponentParentRow :=
  tripleRow 39 16 0 100 183 0 82 16
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber30Row40 : TripleComponentParentRow :=
  tripleRow 40 56 0 101 140 0 103 72
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row41 : TripleComponentParentRow :=
  tripleRow 41 57 0 101 141 0 103 73
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row42 : TripleComponentParentRow :=
  tripleRow 42 58 0 101 142 0 103 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row43 : TripleComponentParentRow :=
  tripleRow 43 40 0 101 143 0 101 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row44 : TripleComponentParentRow :=
  tripleRow 44 40 0 101 188 0 101 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row45 : TripleComponentParentRow :=
  tripleRow 45 41 0 101 189 0 101 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row46 : TripleComponentParentRow :=
  tripleRow 46 62 0 101 190 0 103 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row47 : TripleComponentParentRow :=
  tripleRow 47 63 0 101 191 0 103 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Block0Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row32
  , tttLargeFiber30Row33
  , tttLargeFiber30Row34
  , tttLargeFiber30Row35
  , tttLargeFiber30Row36
  , tttLargeFiber30Row37
  , tttLargeFiber30Row38
  , tttLargeFiber30Row39
  , tttLargeFiber30Row40
  , tttLargeFiber30Row41
  , tttLargeFiber30Row42
  , tttLargeFiber30Row43
  , tttLargeFiber30Row44
  , tttLargeFiber30Row45
  , tttLargeFiber30Row46
  , tttLargeFiber30Row47
  ]

def tttLargeFiber30Block0Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block0Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block0Chunk2ExpectedContains row.source &&
    tttLargeFiber30Block0Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block0Chunk2SourcesCheck : Bool :=
  (tttLargeFiber30Block0Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber30Block0Chunk2Sources

theorem tttLargeFiber30Block0Chunk2SourcesCheck_ok :
    tttLargeFiber30Block0Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber30Block0Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block0Chunk2RowValid
    (listGetD tttLargeFiber30Block0Chunk2Rows i default)

def tttLargeFiber30Block0Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block0Chunk2Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block0Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block0Chunk2Sources 0 0 == 32
      && tttLargeFiber30ParentOf 32 == 48
      && tttLargeFiber30ParentOf 48 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block0Chunk2Sources 1 0 == 33
      && tttLargeFiber30ParentOf 33 == 49
      && tttLargeFiber30ParentOf 49 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block0Chunk2Sources 2 0 == 34
      && tttLargeFiber30ParentOf 34 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block0Chunk2Sources 3 0 == 35
      && tttLargeFiber30ParentOf 35 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block0Chunk2Sources 4 0 == 36
      && tttLargeFiber30ParentOf 36 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block0Chunk2Sources 5 0 == 37
      && tttLargeFiber30ParentOf 37 == 39
      && tttLargeFiber30ParentOf 39 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block0Chunk2Sources 6 0 == 38
      && tttLargeFiber30ParentOf 38 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block0Chunk2Sources 7 0 == 39
      && tttLargeFiber30ParentOf 39 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block0Chunk2Sources 8 0 == 40
      && tttLargeFiber30ParentOf 40 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block0Chunk2Sources 9 0 == 41
      && tttLargeFiber30ParentOf 41 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block0Chunk2Sources 10 0 == 42
      && tttLargeFiber30ParentOf 42 == 58
      && tttLargeFiber30ParentOf 58 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block0Chunk2Sources 11 0 == 43
      && tttLargeFiber30ParentOf 43 == 40
      && tttLargeFiber30ParentOf 40 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block0Chunk2Sources 12 0 == 44
      && tttLargeFiber30ParentOf 44 == 40
      && tttLargeFiber30ParentOf 40 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block0Chunk2Sources 13 0 == 45
      && tttLargeFiber30ParentOf 45 == 41
      && tttLargeFiber30ParentOf 41 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block0Chunk2Sources 14 0 == 46
      && tttLargeFiber30ParentOf 46 == 62
      && tttLargeFiber30ParentOf 62 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block0Chunk2Sources 15 0 == 47
      && tttLargeFiber30ParentOf 47 == 63
      && tttLargeFiber30ParentOf 63 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block0Chunk2Row_0_ok :
    tttLargeFiber30Block0Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_1_ok :
    tttLargeFiber30Block0Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_2_ok :
    tttLargeFiber30Block0Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_3_ok :
    tttLargeFiber30Block0Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_4_ok :
    tttLargeFiber30Block0Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_5_ok :
    tttLargeFiber30Block0Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_6_ok :
    tttLargeFiber30Block0Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_7_ok :
    tttLargeFiber30Block0Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_8_ok :
    tttLargeFiber30Block0Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_9_ok :
    tttLargeFiber30Block0Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_10_ok :
    tttLargeFiber30Block0Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_11_ok :
    tttLargeFiber30Block0Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_12_ok :
    tttLargeFiber30Block0Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_13_ok :
    tttLargeFiber30Block0Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_14_ok :
    tttLargeFiber30Block0Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2Row_15_ok :
    tttLargeFiber30Block0Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_0_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_1_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_2_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_3_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_4_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_5_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_6_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_7_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_8_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_9_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_10_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_11_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_12_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_13_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_14_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentMap_15_ok :
    tttLargeFiber30Block0Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_0_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_1_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_2_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_3_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_4_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_5_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_6_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_7_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_8_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_9_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_10_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_11_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_12_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_13_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_14_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk2ParentPath_15_ok :
    tttLargeFiber30Block0Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block0Chunk2RowsAudit : Bool :=
  tttLargeFiber30Block0Chunk2RowCheck 0
    && tttLargeFiber30Block0Chunk2RowCheck 1
    && tttLargeFiber30Block0Chunk2RowCheck 2
    && tttLargeFiber30Block0Chunk2RowCheck 3
    && tttLargeFiber30Block0Chunk2RowCheck 4
    && tttLargeFiber30Block0Chunk2RowCheck 5
    && tttLargeFiber30Block0Chunk2RowCheck 6
    && tttLargeFiber30Block0Chunk2RowCheck 7
    && tttLargeFiber30Block0Chunk2RowCheck 8
    && tttLargeFiber30Block0Chunk2RowCheck 9
    && tttLargeFiber30Block0Chunk2RowCheck 10
    && tttLargeFiber30Block0Chunk2RowCheck 11
    && tttLargeFiber30Block0Chunk2RowCheck 12
    && tttLargeFiber30Block0Chunk2RowCheck 13
    && tttLargeFiber30Block0Chunk2RowCheck 14
    && tttLargeFiber30Block0Chunk2RowCheck 15

theorem tttLargeFiber30Block0Chunk2RowsAudit_ok :
    tttLargeFiber30Block0Chunk2RowsAudit = true := by
  simp [tttLargeFiber30Block0Chunk2RowsAudit,
    tttLargeFiber30Block0Chunk2Row_0_ok,
    tttLargeFiber30Block0Chunk2Row_1_ok,
    tttLargeFiber30Block0Chunk2Row_2_ok,
    tttLargeFiber30Block0Chunk2Row_3_ok,
    tttLargeFiber30Block0Chunk2Row_4_ok,
    tttLargeFiber30Block0Chunk2Row_5_ok,
    tttLargeFiber30Block0Chunk2Row_6_ok,
    tttLargeFiber30Block0Chunk2Row_7_ok,
    tttLargeFiber30Block0Chunk2Row_8_ok,
    tttLargeFiber30Block0Chunk2Row_9_ok,
    tttLargeFiber30Block0Chunk2Row_10_ok,
    tttLargeFiber30Block0Chunk2Row_11_ok,
    tttLargeFiber30Block0Chunk2Row_12_ok,
    tttLargeFiber30Block0Chunk2Row_13_ok,
    tttLargeFiber30Block0Chunk2Row_14_ok,
    tttLargeFiber30Block0Chunk2Row_15_ok]

def tttLargeFiber30Block0Chunk2ParentMapAudit : Bool :=
  tttLargeFiber30Block0Chunk2ParentMapCheck 0
    && tttLargeFiber30Block0Chunk2ParentMapCheck 1
    && tttLargeFiber30Block0Chunk2ParentMapCheck 2
    && tttLargeFiber30Block0Chunk2ParentMapCheck 3
    && tttLargeFiber30Block0Chunk2ParentMapCheck 4
    && tttLargeFiber30Block0Chunk2ParentMapCheck 5
    && tttLargeFiber30Block0Chunk2ParentMapCheck 6
    && tttLargeFiber30Block0Chunk2ParentMapCheck 7
    && tttLargeFiber30Block0Chunk2ParentMapCheck 8
    && tttLargeFiber30Block0Chunk2ParentMapCheck 9
    && tttLargeFiber30Block0Chunk2ParentMapCheck 10
    && tttLargeFiber30Block0Chunk2ParentMapCheck 11
    && tttLargeFiber30Block0Chunk2ParentMapCheck 12
    && tttLargeFiber30Block0Chunk2ParentMapCheck 13
    && tttLargeFiber30Block0Chunk2ParentMapCheck 14
    && tttLargeFiber30Block0Chunk2ParentMapCheck 15

theorem tttLargeFiber30Block0Chunk2ParentMapAudit_ok :
    tttLargeFiber30Block0Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber30Block0Chunk2ParentMapAudit,
    tttLargeFiber30Block0Chunk2ParentMap_0_ok,
    tttLargeFiber30Block0Chunk2ParentMap_1_ok,
    tttLargeFiber30Block0Chunk2ParentMap_2_ok,
    tttLargeFiber30Block0Chunk2ParentMap_3_ok,
    tttLargeFiber30Block0Chunk2ParentMap_4_ok,
    tttLargeFiber30Block0Chunk2ParentMap_5_ok,
    tttLargeFiber30Block0Chunk2ParentMap_6_ok,
    tttLargeFiber30Block0Chunk2ParentMap_7_ok,
    tttLargeFiber30Block0Chunk2ParentMap_8_ok,
    tttLargeFiber30Block0Chunk2ParentMap_9_ok,
    tttLargeFiber30Block0Chunk2ParentMap_10_ok,
    tttLargeFiber30Block0Chunk2ParentMap_11_ok,
    tttLargeFiber30Block0Chunk2ParentMap_12_ok,
    tttLargeFiber30Block0Chunk2ParentMap_13_ok,
    tttLargeFiber30Block0Chunk2ParentMap_14_ok,
    tttLargeFiber30Block0Chunk2ParentMap_15_ok]

def tttLargeFiber30Block0Chunk2ParentsAudit : Bool :=
  tttLargeFiber30Block0Chunk2ParentPathCheck 0
    && tttLargeFiber30Block0Chunk2ParentPathCheck 1
    && tttLargeFiber30Block0Chunk2ParentPathCheck 2
    && tttLargeFiber30Block0Chunk2ParentPathCheck 3
    && tttLargeFiber30Block0Chunk2ParentPathCheck 4
    && tttLargeFiber30Block0Chunk2ParentPathCheck 5
    && tttLargeFiber30Block0Chunk2ParentPathCheck 6
    && tttLargeFiber30Block0Chunk2ParentPathCheck 7
    && tttLargeFiber30Block0Chunk2ParentPathCheck 8
    && tttLargeFiber30Block0Chunk2ParentPathCheck 9
    && tttLargeFiber30Block0Chunk2ParentPathCheck 10
    && tttLargeFiber30Block0Chunk2ParentPathCheck 11
    && tttLargeFiber30Block0Chunk2ParentPathCheck 12
    && tttLargeFiber30Block0Chunk2ParentPathCheck 13
    && tttLargeFiber30Block0Chunk2ParentPathCheck 14
    && tttLargeFiber30Block0Chunk2ParentPathCheck 15

theorem tttLargeFiber30Block0Chunk2ParentsAudit_ok :
    tttLargeFiber30Block0Chunk2ParentsAudit = true := by
  simp [tttLargeFiber30Block0Chunk2ParentsAudit,
    tttLargeFiber30Block0Chunk2ParentPath_0_ok,
    tttLargeFiber30Block0Chunk2ParentPath_1_ok,
    tttLargeFiber30Block0Chunk2ParentPath_2_ok,
    tttLargeFiber30Block0Chunk2ParentPath_3_ok,
    tttLargeFiber30Block0Chunk2ParentPath_4_ok,
    tttLargeFiber30Block0Chunk2ParentPath_5_ok,
    tttLargeFiber30Block0Chunk2ParentPath_6_ok,
    tttLargeFiber30Block0Chunk2ParentPath_7_ok,
    tttLargeFiber30Block0Chunk2ParentPath_8_ok,
    tttLargeFiber30Block0Chunk2ParentPath_9_ok,
    tttLargeFiber30Block0Chunk2ParentPath_10_ok,
    tttLargeFiber30Block0Chunk2ParentPath_11_ok,
    tttLargeFiber30Block0Chunk2ParentPath_12_ok,
    tttLargeFiber30Block0Chunk2ParentPath_13_ok,
    tttLargeFiber30Block0Chunk2ParentPath_14_ok,
    tttLargeFiber30Block0Chunk2ParentPath_15_ok]

def tttLargeFiber30Block0Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block0Chunk2SourcesCheck &&
    tttLargeFiber30Block0Chunk2RowsAudit &&
    tttLargeFiber30Block0Chunk2ParentMapAudit &&
    tttLargeFiber30Block0Chunk2ParentsAudit

theorem tttLargeFiber30Block0Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber30Block0Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block0Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block0Chunk2SourcesCheck_ok,
    tttLargeFiber30Block0Chunk2RowsAudit_ok,
    tttLargeFiber30Block0Chunk2ParentMapAudit_ok,
    tttLargeFiber30Block0Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block0Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
