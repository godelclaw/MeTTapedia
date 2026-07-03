import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block1Chunk2Sources : List Nat :=
  [   96, 97, 98, 99, 100, 101, 102, 103,
   104, 105, 106, 107, 108, 109, 110, 111]

def tttLargeFiber30Row96 : TripleComponentParentRow :=
  tripleRow 96 32 1 108 132 0 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row97 : TripleComponentParentRow :=
  tripleRow 97 33 1 108 133 0 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row98 : TripleComponentParentRow :=
  tripleRow 98 34 1 108 134 0 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row99 : TripleComponentParentRow :=
  tripleRow 99 35 1 108 135 0 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row100 : TripleComponentParentRow :=
  tripleRow 100 36 1 108 180 0 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row101 : TripleComponentParentRow :=
  tripleRow 101 37 1 108 181 0 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row102 : TripleComponentParentRow :=
  tripleRow 102 38 1 108 182 0 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row103 : TripleComponentParentRow :=
  tripleRow 103 39 1 108 183 0 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row104 : TripleComponentParentRow :=
  tripleRow 104 40 1 109 140 0 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row105 : TripleComponentParentRow :=
  tripleRow 105 41 1 109 141 0 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row106 : TripleComponentParentRow :=
  tripleRow 106 42 1 109 142 0 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row107 : TripleComponentParentRow :=
  tripleRow 107 43 1 109 143 0 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row108 : TripleComponentParentRow :=
  tripleRow 108 44 1 109 188 0 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row109 : TripleComponentParentRow :=
  tripleRow 109 45 1 109 189 0 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row110 : TripleComponentParentRow :=
  tripleRow 110 46 1 109 190 0 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row111 : TripleComponentParentRow :=
  tripleRow 111 47 1 109 191 0 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row96
  , tttLargeFiber30Row97
  , tttLargeFiber30Row98
  , tttLargeFiber30Row99
  , tttLargeFiber30Row100
  , tttLargeFiber30Row101
  , tttLargeFiber30Row102
  , tttLargeFiber30Row103
  , tttLargeFiber30Row104
  , tttLargeFiber30Row105
  , tttLargeFiber30Row106
  , tttLargeFiber30Row107
  , tttLargeFiber30Row108
  , tttLargeFiber30Row109
  , tttLargeFiber30Row110
  , tttLargeFiber30Row111
  ]

def tttLargeFiber30Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber30Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber30Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber30Block1Chunk2Sources

theorem tttLargeFiber30Block1Chunk2SourcesCheck_ok :
    tttLargeFiber30Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber30Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block1Chunk2RowValid
    (listGetD tttLargeFiber30Block1Chunk2Rows i default)

def tttLargeFiber30Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block1Chunk2Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block1Chunk2Sources 0 0 == 96
      && tttLargeFiber30ParentOf 96 == 32
      && tttLargeFiber30ParentOf 32 == 48
      && tttLargeFiber30ParentOf 48 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block1Chunk2Sources 1 0 == 97
      && tttLargeFiber30ParentOf 97 == 33
      && tttLargeFiber30ParentOf 33 == 49
      && tttLargeFiber30ParentOf 49 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block1Chunk2Sources 2 0 == 98
      && tttLargeFiber30ParentOf 98 == 34
      && tttLargeFiber30ParentOf 34 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block1Chunk2Sources 3 0 == 99
      && tttLargeFiber30ParentOf 99 == 35
      && tttLargeFiber30ParentOf 35 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block1Chunk2Sources 4 0 == 100
      && tttLargeFiber30ParentOf 100 == 36
      && tttLargeFiber30ParentOf 36 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block1Chunk2Sources 5 0 == 101
      && tttLargeFiber30ParentOf 101 == 37
      && tttLargeFiber30ParentOf 37 == 39
      && tttLargeFiber30ParentOf 39 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block1Chunk2Sources 6 0 == 102
      && tttLargeFiber30ParentOf 102 == 38
      && tttLargeFiber30ParentOf 38 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block1Chunk2Sources 7 0 == 103
      && tttLargeFiber30ParentOf 103 == 39
      && tttLargeFiber30ParentOf 39 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block1Chunk2Sources 8 0 == 104
      && tttLargeFiber30ParentOf 104 == 40
      && tttLargeFiber30ParentOf 40 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block1Chunk2Sources 9 0 == 105
      && tttLargeFiber30ParentOf 105 == 41
      && tttLargeFiber30ParentOf 41 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block1Chunk2Sources 10 0 == 106
      && tttLargeFiber30ParentOf 106 == 42
      && tttLargeFiber30ParentOf 42 == 58
      && tttLargeFiber30ParentOf 58 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block1Chunk2Sources 11 0 == 107
      && tttLargeFiber30ParentOf 107 == 43
      && tttLargeFiber30ParentOf 43 == 40
      && tttLargeFiber30ParentOf 40 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block1Chunk2Sources 12 0 == 108
      && tttLargeFiber30ParentOf 108 == 44
      && tttLargeFiber30ParentOf 44 == 40
      && tttLargeFiber30ParentOf 40 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block1Chunk2Sources 13 0 == 109
      && tttLargeFiber30ParentOf 109 == 45
      && tttLargeFiber30ParentOf 45 == 41
      && tttLargeFiber30ParentOf 41 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block1Chunk2Sources 14 0 == 110
      && tttLargeFiber30ParentOf 110 == 46
      && tttLargeFiber30ParentOf 46 == 62
      && tttLargeFiber30ParentOf 62 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block1Chunk2Sources 15 0 == 111
      && tttLargeFiber30ParentOf 111 == 47
      && tttLargeFiber30ParentOf 47 == 63
      && tttLargeFiber30ParentOf 63 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block1Chunk2Row_0_ok :
    tttLargeFiber30Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_1_ok :
    tttLargeFiber30Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_2_ok :
    tttLargeFiber30Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_3_ok :
    tttLargeFiber30Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_4_ok :
    tttLargeFiber30Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_5_ok :
    tttLargeFiber30Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_6_ok :
    tttLargeFiber30Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_7_ok :
    tttLargeFiber30Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_8_ok :
    tttLargeFiber30Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_9_ok :
    tttLargeFiber30Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_10_ok :
    tttLargeFiber30Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_11_ok :
    tttLargeFiber30Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_12_ok :
    tttLargeFiber30Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_13_ok :
    tttLargeFiber30Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_14_ok :
    tttLargeFiber30Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2Row_15_ok :
    tttLargeFiber30Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_0_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_1_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_2_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_3_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_4_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_5_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_6_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_7_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_8_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_9_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_10_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_11_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_12_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_13_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_14_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentMap_15_ok :
    tttLargeFiber30Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_0_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_1_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_2_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_3_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_4_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_5_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_6_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_7_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_8_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_9_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_10_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_11_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_12_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_13_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_14_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk2ParentPath_15_ok :
    tttLargeFiber30Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber30Block1Chunk2RowCheck 0
    && tttLargeFiber30Block1Chunk2RowCheck 1
    && tttLargeFiber30Block1Chunk2RowCheck 2
    && tttLargeFiber30Block1Chunk2RowCheck 3
    && tttLargeFiber30Block1Chunk2RowCheck 4
    && tttLargeFiber30Block1Chunk2RowCheck 5
    && tttLargeFiber30Block1Chunk2RowCheck 6
    && tttLargeFiber30Block1Chunk2RowCheck 7
    && tttLargeFiber30Block1Chunk2RowCheck 8
    && tttLargeFiber30Block1Chunk2RowCheck 9
    && tttLargeFiber30Block1Chunk2RowCheck 10
    && tttLargeFiber30Block1Chunk2RowCheck 11
    && tttLargeFiber30Block1Chunk2RowCheck 12
    && tttLargeFiber30Block1Chunk2RowCheck 13
    && tttLargeFiber30Block1Chunk2RowCheck 14
    && tttLargeFiber30Block1Chunk2RowCheck 15

theorem tttLargeFiber30Block1Chunk2RowsAudit_ok :
    tttLargeFiber30Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber30Block1Chunk2RowsAudit,
    tttLargeFiber30Block1Chunk2Row_0_ok,
    tttLargeFiber30Block1Chunk2Row_1_ok,
    tttLargeFiber30Block1Chunk2Row_2_ok,
    tttLargeFiber30Block1Chunk2Row_3_ok,
    tttLargeFiber30Block1Chunk2Row_4_ok,
    tttLargeFiber30Block1Chunk2Row_5_ok,
    tttLargeFiber30Block1Chunk2Row_6_ok,
    tttLargeFiber30Block1Chunk2Row_7_ok,
    tttLargeFiber30Block1Chunk2Row_8_ok,
    tttLargeFiber30Block1Chunk2Row_9_ok,
    tttLargeFiber30Block1Chunk2Row_10_ok,
    tttLargeFiber30Block1Chunk2Row_11_ok,
    tttLargeFiber30Block1Chunk2Row_12_ok,
    tttLargeFiber30Block1Chunk2Row_13_ok,
    tttLargeFiber30Block1Chunk2Row_14_ok,
    tttLargeFiber30Block1Chunk2Row_15_ok]

def tttLargeFiber30Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber30Block1Chunk2ParentMapCheck 0
    && tttLargeFiber30Block1Chunk2ParentMapCheck 1
    && tttLargeFiber30Block1Chunk2ParentMapCheck 2
    && tttLargeFiber30Block1Chunk2ParentMapCheck 3
    && tttLargeFiber30Block1Chunk2ParentMapCheck 4
    && tttLargeFiber30Block1Chunk2ParentMapCheck 5
    && tttLargeFiber30Block1Chunk2ParentMapCheck 6
    && tttLargeFiber30Block1Chunk2ParentMapCheck 7
    && tttLargeFiber30Block1Chunk2ParentMapCheck 8
    && tttLargeFiber30Block1Chunk2ParentMapCheck 9
    && tttLargeFiber30Block1Chunk2ParentMapCheck 10
    && tttLargeFiber30Block1Chunk2ParentMapCheck 11
    && tttLargeFiber30Block1Chunk2ParentMapCheck 12
    && tttLargeFiber30Block1Chunk2ParentMapCheck 13
    && tttLargeFiber30Block1Chunk2ParentMapCheck 14
    && tttLargeFiber30Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber30Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber30Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber30Block1Chunk2ParentMapAudit,
    tttLargeFiber30Block1Chunk2ParentMap_0_ok,
    tttLargeFiber30Block1Chunk2ParentMap_1_ok,
    tttLargeFiber30Block1Chunk2ParentMap_2_ok,
    tttLargeFiber30Block1Chunk2ParentMap_3_ok,
    tttLargeFiber30Block1Chunk2ParentMap_4_ok,
    tttLargeFiber30Block1Chunk2ParentMap_5_ok,
    tttLargeFiber30Block1Chunk2ParentMap_6_ok,
    tttLargeFiber30Block1Chunk2ParentMap_7_ok,
    tttLargeFiber30Block1Chunk2ParentMap_8_ok,
    tttLargeFiber30Block1Chunk2ParentMap_9_ok,
    tttLargeFiber30Block1Chunk2ParentMap_10_ok,
    tttLargeFiber30Block1Chunk2ParentMap_11_ok,
    tttLargeFiber30Block1Chunk2ParentMap_12_ok,
    tttLargeFiber30Block1Chunk2ParentMap_13_ok,
    tttLargeFiber30Block1Chunk2ParentMap_14_ok,
    tttLargeFiber30Block1Chunk2ParentMap_15_ok]

def tttLargeFiber30Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber30Block1Chunk2ParentPathCheck 0
    && tttLargeFiber30Block1Chunk2ParentPathCheck 1
    && tttLargeFiber30Block1Chunk2ParentPathCheck 2
    && tttLargeFiber30Block1Chunk2ParentPathCheck 3
    && tttLargeFiber30Block1Chunk2ParentPathCheck 4
    && tttLargeFiber30Block1Chunk2ParentPathCheck 5
    && tttLargeFiber30Block1Chunk2ParentPathCheck 6
    && tttLargeFiber30Block1Chunk2ParentPathCheck 7
    && tttLargeFiber30Block1Chunk2ParentPathCheck 8
    && tttLargeFiber30Block1Chunk2ParentPathCheck 9
    && tttLargeFiber30Block1Chunk2ParentPathCheck 10
    && tttLargeFiber30Block1Chunk2ParentPathCheck 11
    && tttLargeFiber30Block1Chunk2ParentPathCheck 12
    && tttLargeFiber30Block1Chunk2ParentPathCheck 13
    && tttLargeFiber30Block1Chunk2ParentPathCheck 14
    && tttLargeFiber30Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber30Block1Chunk2ParentsAudit_ok :
    tttLargeFiber30Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber30Block1Chunk2ParentsAudit,
    tttLargeFiber30Block1Chunk2ParentPath_0_ok,
    tttLargeFiber30Block1Chunk2ParentPath_1_ok,
    tttLargeFiber30Block1Chunk2ParentPath_2_ok,
    tttLargeFiber30Block1Chunk2ParentPath_3_ok,
    tttLargeFiber30Block1Chunk2ParentPath_4_ok,
    tttLargeFiber30Block1Chunk2ParentPath_5_ok,
    tttLargeFiber30Block1Chunk2ParentPath_6_ok,
    tttLargeFiber30Block1Chunk2ParentPath_7_ok,
    tttLargeFiber30Block1Chunk2ParentPath_8_ok,
    tttLargeFiber30Block1Chunk2ParentPath_9_ok,
    tttLargeFiber30Block1Chunk2ParentPath_10_ok,
    tttLargeFiber30Block1Chunk2ParentPath_11_ok,
    tttLargeFiber30Block1Chunk2ParentPath_12_ok,
    tttLargeFiber30Block1Chunk2ParentPath_13_ok,
    tttLargeFiber30Block1Chunk2ParentPath_14_ok,
    tttLargeFiber30Block1Chunk2ParentPath_15_ok]

def tttLargeFiber30Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block1Chunk2SourcesCheck &&
    tttLargeFiber30Block1Chunk2RowsAudit &&
    tttLargeFiber30Block1Chunk2ParentMapAudit &&
    tttLargeFiber30Block1Chunk2ParentsAudit

theorem tttLargeFiber30Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber30Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block1Chunk2SourcesCheck_ok,
    tttLargeFiber30Block1Chunk2RowsAudit_ok,
    tttLargeFiber30Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber30Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
