import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 5 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block5Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block5Chunk0Sources : List Nat :=
  [   1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703,
   1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]

def tttLargeFiber30Row320 : TripleComponentParentRow :=
  tripleRow 1696 64 49 156 148 1 88 80
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row321 : TripleComponentParentRow :=
  tripleRow 1697 65 49 156 149 1 88 81
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row322 : TripleComponentParentRow :=
  tripleRow 1698 66 49 156 150 1 88 82
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row323 : TripleComponentParentRow :=
  tripleRow 1699 1696 49 156 151 49 156 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row324 : TripleComponentParentRow :=
  tripleRow 1700 1696 49 156 164 49 156 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row325 : TripleComponentParentRow :=
  tripleRow 1701 1697 49 156 165 49 156 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row326 : TripleComponentParentRow :=
  tripleRow 1702 70 49 156 166 1 88 102
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row327 : TripleComponentParentRow :=
  tripleRow 1703 71 49 156 167 1 88 103
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row328 : TripleComponentParentRow :=
  tripleRow 1704 72 49 157 156 1 89 88
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row329 : TripleComponentParentRow :=
  tripleRow 1705 73 49 157 157 1 89 89
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row330 : TripleComponentParentRow :=
  tripleRow 1706 74 49 157 158 1 89 90
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row331 : TripleComponentParentRow :=
  tripleRow 1707 1704 49 157 159 49 157 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row332 : TripleComponentParentRow :=
  tripleRow 1708 1704 49 157 172 49 157 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row333 : TripleComponentParentRow :=
  tripleRow 1709 1705 49 157 173 49 157 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row334 : TripleComponentParentRow :=
  tripleRow 1710 78 49 157 174 1 89 110
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row335 : TripleComponentParentRow :=
  tripleRow 1711 79 49 157 175 1 89 111
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Block5Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row320
  , tttLargeFiber30Row321
  , tttLargeFiber30Row322
  , tttLargeFiber30Row323
  , tttLargeFiber30Row324
  , tttLargeFiber30Row325
  , tttLargeFiber30Row326
  , tttLargeFiber30Row327
  , tttLargeFiber30Row328
  , tttLargeFiber30Row329
  , tttLargeFiber30Row330
  , tttLargeFiber30Row331
  , tttLargeFiber30Row332
  , tttLargeFiber30Row333
  , tttLargeFiber30Row334
  , tttLargeFiber30Row335
  ]

def tttLargeFiber30Block5Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block5Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block5Chunk0ExpectedContains row.source &&
    tttLargeFiber30Block5Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block5Chunk0SourcesCheck : Bool :=
  (tttLargeFiber30Block5Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber30Block5Chunk0Sources

theorem tttLargeFiber30Block5Chunk0SourcesCheck_ok :
    tttLargeFiber30Block5Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber30Block5Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block5Chunk0RowValid
    (listGetD tttLargeFiber30Block5Chunk0Rows i default)

def tttLargeFiber30Block5Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block5Chunk0Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block5Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block5Chunk0Sources 0 0 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block5Chunk0Sources 1 0 == 1697
      && tttLargeFiber30ParentOf 1697 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block5Chunk0Sources 2 0 == 1698
      && tttLargeFiber30ParentOf 1698 == 66
      && tttLargeFiber30ParentOf 66 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block5Chunk0Sources 3 0 == 1699
      && tttLargeFiber30ParentOf 1699 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block5Chunk0Sources 4 0 == 1700
      && tttLargeFiber30ParentOf 1700 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block5Chunk0Sources 5 0 == 1701
      && tttLargeFiber30ParentOf 1701 == 1697
      && tttLargeFiber30ParentOf 1697 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block5Chunk0Sources 6 0 == 1702
      && tttLargeFiber30ParentOf 1702 == 70
      && tttLargeFiber30ParentOf 70 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block5Chunk0Sources 7 0 == 1703
      && tttLargeFiber30ParentOf 1703 == 71
      && tttLargeFiber30ParentOf 71 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block5Chunk0Sources 8 0 == 1704
      && tttLargeFiber30ParentOf 1704 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block5Chunk0Sources 9 0 == 1705
      && tttLargeFiber30ParentOf 1705 == 73
      && tttLargeFiber30ParentOf 73 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block5Chunk0Sources 10 0 == 1706
      && tttLargeFiber30ParentOf 1706 == 74
      && tttLargeFiber30ParentOf 74 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block5Chunk0Sources 11 0 == 1707
      && tttLargeFiber30ParentOf 1707 == 1704
      && tttLargeFiber30ParentOf 1704 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block5Chunk0Sources 12 0 == 1708
      && tttLargeFiber30ParentOf 1708 == 1704
      && tttLargeFiber30ParentOf 1704 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block5Chunk0Sources 13 0 == 1709
      && tttLargeFiber30ParentOf 1709 == 1705
      && tttLargeFiber30ParentOf 1705 == 73
      && tttLargeFiber30ParentOf 73 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block5Chunk0Sources 14 0 == 1710
      && tttLargeFiber30ParentOf 1710 == 78
      && tttLargeFiber30ParentOf 78 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block5Chunk0Sources 15 0 == 1711
      && tttLargeFiber30ParentOf 1711 == 79
      && tttLargeFiber30ParentOf 79 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block5Chunk0Row_0_ok :
    tttLargeFiber30Block5Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_1_ok :
    tttLargeFiber30Block5Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_2_ok :
    tttLargeFiber30Block5Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_3_ok :
    tttLargeFiber30Block5Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_4_ok :
    tttLargeFiber30Block5Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_5_ok :
    tttLargeFiber30Block5Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_6_ok :
    tttLargeFiber30Block5Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_7_ok :
    tttLargeFiber30Block5Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_8_ok :
    tttLargeFiber30Block5Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_9_ok :
    tttLargeFiber30Block5Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_10_ok :
    tttLargeFiber30Block5Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_11_ok :
    tttLargeFiber30Block5Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_12_ok :
    tttLargeFiber30Block5Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_13_ok :
    tttLargeFiber30Block5Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_14_ok :
    tttLargeFiber30Block5Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0Row_15_ok :
    tttLargeFiber30Block5Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_0_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_1_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_2_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_3_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_4_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_5_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_6_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_7_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_8_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_9_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_10_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_11_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_12_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_13_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_14_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentMap_15_ok :
    tttLargeFiber30Block5Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_0_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_1_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_2_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_3_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_4_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_5_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_6_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_7_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_8_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_9_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_10_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_11_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_12_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_13_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_14_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk0ParentPath_15_ok :
    tttLargeFiber30Block5Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block5Chunk0RowsAudit : Bool :=
  tttLargeFiber30Block5Chunk0RowCheck 0
    && tttLargeFiber30Block5Chunk0RowCheck 1
    && tttLargeFiber30Block5Chunk0RowCheck 2
    && tttLargeFiber30Block5Chunk0RowCheck 3
    && tttLargeFiber30Block5Chunk0RowCheck 4
    && tttLargeFiber30Block5Chunk0RowCheck 5
    && tttLargeFiber30Block5Chunk0RowCheck 6
    && tttLargeFiber30Block5Chunk0RowCheck 7
    && tttLargeFiber30Block5Chunk0RowCheck 8
    && tttLargeFiber30Block5Chunk0RowCheck 9
    && tttLargeFiber30Block5Chunk0RowCheck 10
    && tttLargeFiber30Block5Chunk0RowCheck 11
    && tttLargeFiber30Block5Chunk0RowCheck 12
    && tttLargeFiber30Block5Chunk0RowCheck 13
    && tttLargeFiber30Block5Chunk0RowCheck 14
    && tttLargeFiber30Block5Chunk0RowCheck 15

theorem tttLargeFiber30Block5Chunk0RowsAudit_ok :
    tttLargeFiber30Block5Chunk0RowsAudit = true := by
  simp [tttLargeFiber30Block5Chunk0RowsAudit,
    tttLargeFiber30Block5Chunk0Row_0_ok,
    tttLargeFiber30Block5Chunk0Row_1_ok,
    tttLargeFiber30Block5Chunk0Row_2_ok,
    tttLargeFiber30Block5Chunk0Row_3_ok,
    tttLargeFiber30Block5Chunk0Row_4_ok,
    tttLargeFiber30Block5Chunk0Row_5_ok,
    tttLargeFiber30Block5Chunk0Row_6_ok,
    tttLargeFiber30Block5Chunk0Row_7_ok,
    tttLargeFiber30Block5Chunk0Row_8_ok,
    tttLargeFiber30Block5Chunk0Row_9_ok,
    tttLargeFiber30Block5Chunk0Row_10_ok,
    tttLargeFiber30Block5Chunk0Row_11_ok,
    tttLargeFiber30Block5Chunk0Row_12_ok,
    tttLargeFiber30Block5Chunk0Row_13_ok,
    tttLargeFiber30Block5Chunk0Row_14_ok,
    tttLargeFiber30Block5Chunk0Row_15_ok]

def tttLargeFiber30Block5Chunk0ParentMapAudit : Bool :=
  tttLargeFiber30Block5Chunk0ParentMapCheck 0
    && tttLargeFiber30Block5Chunk0ParentMapCheck 1
    && tttLargeFiber30Block5Chunk0ParentMapCheck 2
    && tttLargeFiber30Block5Chunk0ParentMapCheck 3
    && tttLargeFiber30Block5Chunk0ParentMapCheck 4
    && tttLargeFiber30Block5Chunk0ParentMapCheck 5
    && tttLargeFiber30Block5Chunk0ParentMapCheck 6
    && tttLargeFiber30Block5Chunk0ParentMapCheck 7
    && tttLargeFiber30Block5Chunk0ParentMapCheck 8
    && tttLargeFiber30Block5Chunk0ParentMapCheck 9
    && tttLargeFiber30Block5Chunk0ParentMapCheck 10
    && tttLargeFiber30Block5Chunk0ParentMapCheck 11
    && tttLargeFiber30Block5Chunk0ParentMapCheck 12
    && tttLargeFiber30Block5Chunk0ParentMapCheck 13
    && tttLargeFiber30Block5Chunk0ParentMapCheck 14
    && tttLargeFiber30Block5Chunk0ParentMapCheck 15

theorem tttLargeFiber30Block5Chunk0ParentMapAudit_ok :
    tttLargeFiber30Block5Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber30Block5Chunk0ParentMapAudit,
    tttLargeFiber30Block5Chunk0ParentMap_0_ok,
    tttLargeFiber30Block5Chunk0ParentMap_1_ok,
    tttLargeFiber30Block5Chunk0ParentMap_2_ok,
    tttLargeFiber30Block5Chunk0ParentMap_3_ok,
    tttLargeFiber30Block5Chunk0ParentMap_4_ok,
    tttLargeFiber30Block5Chunk0ParentMap_5_ok,
    tttLargeFiber30Block5Chunk0ParentMap_6_ok,
    tttLargeFiber30Block5Chunk0ParentMap_7_ok,
    tttLargeFiber30Block5Chunk0ParentMap_8_ok,
    tttLargeFiber30Block5Chunk0ParentMap_9_ok,
    tttLargeFiber30Block5Chunk0ParentMap_10_ok,
    tttLargeFiber30Block5Chunk0ParentMap_11_ok,
    tttLargeFiber30Block5Chunk0ParentMap_12_ok,
    tttLargeFiber30Block5Chunk0ParentMap_13_ok,
    tttLargeFiber30Block5Chunk0ParentMap_14_ok,
    tttLargeFiber30Block5Chunk0ParentMap_15_ok]

def tttLargeFiber30Block5Chunk0ParentsAudit : Bool :=
  tttLargeFiber30Block5Chunk0ParentPathCheck 0
    && tttLargeFiber30Block5Chunk0ParentPathCheck 1
    && tttLargeFiber30Block5Chunk0ParentPathCheck 2
    && tttLargeFiber30Block5Chunk0ParentPathCheck 3
    && tttLargeFiber30Block5Chunk0ParentPathCheck 4
    && tttLargeFiber30Block5Chunk0ParentPathCheck 5
    && tttLargeFiber30Block5Chunk0ParentPathCheck 6
    && tttLargeFiber30Block5Chunk0ParentPathCheck 7
    && tttLargeFiber30Block5Chunk0ParentPathCheck 8
    && tttLargeFiber30Block5Chunk0ParentPathCheck 9
    && tttLargeFiber30Block5Chunk0ParentPathCheck 10
    && tttLargeFiber30Block5Chunk0ParentPathCheck 11
    && tttLargeFiber30Block5Chunk0ParentPathCheck 12
    && tttLargeFiber30Block5Chunk0ParentPathCheck 13
    && tttLargeFiber30Block5Chunk0ParentPathCheck 14
    && tttLargeFiber30Block5Chunk0ParentPathCheck 15

theorem tttLargeFiber30Block5Chunk0ParentsAudit_ok :
    tttLargeFiber30Block5Chunk0ParentsAudit = true := by
  simp [tttLargeFiber30Block5Chunk0ParentsAudit,
    tttLargeFiber30Block5Chunk0ParentPath_0_ok,
    tttLargeFiber30Block5Chunk0ParentPath_1_ok,
    tttLargeFiber30Block5Chunk0ParentPath_2_ok,
    tttLargeFiber30Block5Chunk0ParentPath_3_ok,
    tttLargeFiber30Block5Chunk0ParentPath_4_ok,
    tttLargeFiber30Block5Chunk0ParentPath_5_ok,
    tttLargeFiber30Block5Chunk0ParentPath_6_ok,
    tttLargeFiber30Block5Chunk0ParentPath_7_ok,
    tttLargeFiber30Block5Chunk0ParentPath_8_ok,
    tttLargeFiber30Block5Chunk0ParentPath_9_ok,
    tttLargeFiber30Block5Chunk0ParentPath_10_ok,
    tttLargeFiber30Block5Chunk0ParentPath_11_ok,
    tttLargeFiber30Block5Chunk0ParentPath_12_ok,
    tttLargeFiber30Block5Chunk0ParentPath_13_ok,
    tttLargeFiber30Block5Chunk0ParentPath_14_ok,
    tttLargeFiber30Block5Chunk0ParentPath_15_ok]

def tttLargeFiber30Block5Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block5Chunk0SourcesCheck &&
    tttLargeFiber30Block5Chunk0RowsAudit &&
    tttLargeFiber30Block5Chunk0ParentMapAudit &&
    tttLargeFiber30Block5Chunk0ParentsAudit

theorem tttLargeFiber30Block5Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber30Block5Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block5Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block5Chunk0SourcesCheck_ok,
    tttLargeFiber30Block5Chunk0RowsAudit_ok,
    tttLargeFiber30Block5Chunk0ParentMapAudit_ok,
    tttLargeFiber30Block5Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block5Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
