import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 4 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block4Chunk0Sources : List Nat :=
  [   1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639,
   1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]

def tttLargeFiber30Row256 : TripleComponentParentRow :=
  tripleRow 1632 0 48 148 148 0 80 80
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

def tttLargeFiber30Row257 : TripleComponentParentRow :=
  tripleRow 1633 1 48 148 149 0 80 81
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

def tttLargeFiber30Row258 : TripleComponentParentRow :=
  tripleRow 1634 2 48 148 150 0 80 82
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

def tttLargeFiber30Row259 : TripleComponentParentRow :=
  tripleRow 1635 1632 48 148 151 48 148 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row260 : TripleComponentParentRow :=
  tripleRow 1636 1632 48 148 164 48 148 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row261 : TripleComponentParentRow :=
  tripleRow 1637 1633 48 148 165 48 148 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row262 : TripleComponentParentRow :=
  tripleRow 1638 6 48 148 166 0 80 102
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

def tttLargeFiber30Row263 : TripleComponentParentRow :=
  tripleRow 1639 7 48 148 167 0 80 103
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

def tttLargeFiber30Row264 : TripleComponentParentRow :=
  tripleRow 1640 8 48 149 156 0 81 88
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

def tttLargeFiber30Row265 : TripleComponentParentRow :=
  tripleRow 1641 9 48 149 157 0 81 89
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

def tttLargeFiber30Row266 : TripleComponentParentRow :=
  tripleRow 1642 10 48 149 158 0 81 90
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

def tttLargeFiber30Row267 : TripleComponentParentRow :=
  tripleRow 1643 1640 48 149 159 48 149 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row268 : TripleComponentParentRow :=
  tripleRow 1644 1640 48 149 172 48 149 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row269 : TripleComponentParentRow :=
  tripleRow 1645 1641 48 149 173 48 149 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row270 : TripleComponentParentRow :=
  tripleRow 1646 14 48 149 174 0 81 110
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

def tttLargeFiber30Row271 : TripleComponentParentRow :=
  tripleRow 1647 15 48 149 175 0 81 111
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

def tttLargeFiber30Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row256
  , tttLargeFiber30Row257
  , tttLargeFiber30Row258
  , tttLargeFiber30Row259
  , tttLargeFiber30Row260
  , tttLargeFiber30Row261
  , tttLargeFiber30Row262
  , tttLargeFiber30Row263
  , tttLargeFiber30Row264
  , tttLargeFiber30Row265
  , tttLargeFiber30Row266
  , tttLargeFiber30Row267
  , tttLargeFiber30Row268
  , tttLargeFiber30Row269
  , tttLargeFiber30Row270
  , tttLargeFiber30Row271
  ]

def tttLargeFiber30Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber30Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber30Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber30Block4Chunk0Sources

theorem tttLargeFiber30Block4Chunk0SourcesCheck_ok :
    tttLargeFiber30Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber30Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block4Chunk0RowValid
    (listGetD tttLargeFiber30Block4Chunk0Rows i default)

def tttLargeFiber30Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block4Chunk0Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block4Chunk0Sources 0 0 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block4Chunk0Sources 1 0 == 1633
      && tttLargeFiber30ParentOf 1633 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block4Chunk0Sources 2 0 == 1634
      && tttLargeFiber30ParentOf 1634 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block4Chunk0Sources 3 0 == 1635
      && tttLargeFiber30ParentOf 1635 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block4Chunk0Sources 4 0 == 1636
      && tttLargeFiber30ParentOf 1636 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block4Chunk0Sources 5 0 == 1637
      && tttLargeFiber30ParentOf 1637 == 1633
      && tttLargeFiber30ParentOf 1633 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block4Chunk0Sources 6 0 == 1638
      && tttLargeFiber30ParentOf 1638 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block4Chunk0Sources 7 0 == 1639
      && tttLargeFiber30ParentOf 1639 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block4Chunk0Sources 8 0 == 1640
      && tttLargeFiber30ParentOf 1640 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block4Chunk0Sources 9 0 == 1641
      && tttLargeFiber30ParentOf 1641 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block4Chunk0Sources 10 0 == 1642
      && tttLargeFiber30ParentOf 1642 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block4Chunk0Sources 11 0 == 1643
      && tttLargeFiber30ParentOf 1643 == 1640
      && tttLargeFiber30ParentOf 1640 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block4Chunk0Sources 12 0 == 1644
      && tttLargeFiber30ParentOf 1644 == 1640
      && tttLargeFiber30ParentOf 1640 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block4Chunk0Sources 13 0 == 1645
      && tttLargeFiber30ParentOf 1645 == 1641
      && tttLargeFiber30ParentOf 1641 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block4Chunk0Sources 14 0 == 1646
      && tttLargeFiber30ParentOf 1646 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block4Chunk0Sources 15 0 == 1647
      && tttLargeFiber30ParentOf 1647 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block4Chunk0Row_0_ok :
    tttLargeFiber30Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_1_ok :
    tttLargeFiber30Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_2_ok :
    tttLargeFiber30Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_3_ok :
    tttLargeFiber30Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_4_ok :
    tttLargeFiber30Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_5_ok :
    tttLargeFiber30Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_6_ok :
    tttLargeFiber30Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_7_ok :
    tttLargeFiber30Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_8_ok :
    tttLargeFiber30Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_9_ok :
    tttLargeFiber30Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_10_ok :
    tttLargeFiber30Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_11_ok :
    tttLargeFiber30Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_12_ok :
    tttLargeFiber30Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_13_ok :
    tttLargeFiber30Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_14_ok :
    tttLargeFiber30Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0Row_15_ok :
    tttLargeFiber30Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_0_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_1_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_2_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_3_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_4_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_5_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_6_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_7_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_8_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_9_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_10_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_11_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_12_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_13_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_14_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentMap_15_ok :
    tttLargeFiber30Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_0_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_1_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_2_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_3_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_4_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_5_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_6_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_7_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_8_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_9_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_10_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_11_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_12_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_13_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_14_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk0ParentPath_15_ok :
    tttLargeFiber30Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber30Block4Chunk0RowCheck 0
    && tttLargeFiber30Block4Chunk0RowCheck 1
    && tttLargeFiber30Block4Chunk0RowCheck 2
    && tttLargeFiber30Block4Chunk0RowCheck 3
    && tttLargeFiber30Block4Chunk0RowCheck 4
    && tttLargeFiber30Block4Chunk0RowCheck 5
    && tttLargeFiber30Block4Chunk0RowCheck 6
    && tttLargeFiber30Block4Chunk0RowCheck 7
    && tttLargeFiber30Block4Chunk0RowCheck 8
    && tttLargeFiber30Block4Chunk0RowCheck 9
    && tttLargeFiber30Block4Chunk0RowCheck 10
    && tttLargeFiber30Block4Chunk0RowCheck 11
    && tttLargeFiber30Block4Chunk0RowCheck 12
    && tttLargeFiber30Block4Chunk0RowCheck 13
    && tttLargeFiber30Block4Chunk0RowCheck 14
    && tttLargeFiber30Block4Chunk0RowCheck 15

theorem tttLargeFiber30Block4Chunk0RowsAudit_ok :
    tttLargeFiber30Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber30Block4Chunk0RowsAudit,
    tttLargeFiber30Block4Chunk0Row_0_ok,
    tttLargeFiber30Block4Chunk0Row_1_ok,
    tttLargeFiber30Block4Chunk0Row_2_ok,
    tttLargeFiber30Block4Chunk0Row_3_ok,
    tttLargeFiber30Block4Chunk0Row_4_ok,
    tttLargeFiber30Block4Chunk0Row_5_ok,
    tttLargeFiber30Block4Chunk0Row_6_ok,
    tttLargeFiber30Block4Chunk0Row_7_ok,
    tttLargeFiber30Block4Chunk0Row_8_ok,
    tttLargeFiber30Block4Chunk0Row_9_ok,
    tttLargeFiber30Block4Chunk0Row_10_ok,
    tttLargeFiber30Block4Chunk0Row_11_ok,
    tttLargeFiber30Block4Chunk0Row_12_ok,
    tttLargeFiber30Block4Chunk0Row_13_ok,
    tttLargeFiber30Block4Chunk0Row_14_ok,
    tttLargeFiber30Block4Chunk0Row_15_ok]

def tttLargeFiber30Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber30Block4Chunk0ParentMapCheck 0
    && tttLargeFiber30Block4Chunk0ParentMapCheck 1
    && tttLargeFiber30Block4Chunk0ParentMapCheck 2
    && tttLargeFiber30Block4Chunk0ParentMapCheck 3
    && tttLargeFiber30Block4Chunk0ParentMapCheck 4
    && tttLargeFiber30Block4Chunk0ParentMapCheck 5
    && tttLargeFiber30Block4Chunk0ParentMapCheck 6
    && tttLargeFiber30Block4Chunk0ParentMapCheck 7
    && tttLargeFiber30Block4Chunk0ParentMapCheck 8
    && tttLargeFiber30Block4Chunk0ParentMapCheck 9
    && tttLargeFiber30Block4Chunk0ParentMapCheck 10
    && tttLargeFiber30Block4Chunk0ParentMapCheck 11
    && tttLargeFiber30Block4Chunk0ParentMapCheck 12
    && tttLargeFiber30Block4Chunk0ParentMapCheck 13
    && tttLargeFiber30Block4Chunk0ParentMapCheck 14
    && tttLargeFiber30Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber30Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber30Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber30Block4Chunk0ParentMapAudit,
    tttLargeFiber30Block4Chunk0ParentMap_0_ok,
    tttLargeFiber30Block4Chunk0ParentMap_1_ok,
    tttLargeFiber30Block4Chunk0ParentMap_2_ok,
    tttLargeFiber30Block4Chunk0ParentMap_3_ok,
    tttLargeFiber30Block4Chunk0ParentMap_4_ok,
    tttLargeFiber30Block4Chunk0ParentMap_5_ok,
    tttLargeFiber30Block4Chunk0ParentMap_6_ok,
    tttLargeFiber30Block4Chunk0ParentMap_7_ok,
    tttLargeFiber30Block4Chunk0ParentMap_8_ok,
    tttLargeFiber30Block4Chunk0ParentMap_9_ok,
    tttLargeFiber30Block4Chunk0ParentMap_10_ok,
    tttLargeFiber30Block4Chunk0ParentMap_11_ok,
    tttLargeFiber30Block4Chunk0ParentMap_12_ok,
    tttLargeFiber30Block4Chunk0ParentMap_13_ok,
    tttLargeFiber30Block4Chunk0ParentMap_14_ok,
    tttLargeFiber30Block4Chunk0ParentMap_15_ok]

def tttLargeFiber30Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber30Block4Chunk0ParentPathCheck 0
    && tttLargeFiber30Block4Chunk0ParentPathCheck 1
    && tttLargeFiber30Block4Chunk0ParentPathCheck 2
    && tttLargeFiber30Block4Chunk0ParentPathCheck 3
    && tttLargeFiber30Block4Chunk0ParentPathCheck 4
    && tttLargeFiber30Block4Chunk0ParentPathCheck 5
    && tttLargeFiber30Block4Chunk0ParentPathCheck 6
    && tttLargeFiber30Block4Chunk0ParentPathCheck 7
    && tttLargeFiber30Block4Chunk0ParentPathCheck 8
    && tttLargeFiber30Block4Chunk0ParentPathCheck 9
    && tttLargeFiber30Block4Chunk0ParentPathCheck 10
    && tttLargeFiber30Block4Chunk0ParentPathCheck 11
    && tttLargeFiber30Block4Chunk0ParentPathCheck 12
    && tttLargeFiber30Block4Chunk0ParentPathCheck 13
    && tttLargeFiber30Block4Chunk0ParentPathCheck 14
    && tttLargeFiber30Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber30Block4Chunk0ParentsAudit_ok :
    tttLargeFiber30Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber30Block4Chunk0ParentsAudit,
    tttLargeFiber30Block4Chunk0ParentPath_0_ok,
    tttLargeFiber30Block4Chunk0ParentPath_1_ok,
    tttLargeFiber30Block4Chunk0ParentPath_2_ok,
    tttLargeFiber30Block4Chunk0ParentPath_3_ok,
    tttLargeFiber30Block4Chunk0ParentPath_4_ok,
    tttLargeFiber30Block4Chunk0ParentPath_5_ok,
    tttLargeFiber30Block4Chunk0ParentPath_6_ok,
    tttLargeFiber30Block4Chunk0ParentPath_7_ok,
    tttLargeFiber30Block4Chunk0ParentPath_8_ok,
    tttLargeFiber30Block4Chunk0ParentPath_9_ok,
    tttLargeFiber30Block4Chunk0ParentPath_10_ok,
    tttLargeFiber30Block4Chunk0ParentPath_11_ok,
    tttLargeFiber30Block4Chunk0ParentPath_12_ok,
    tttLargeFiber30Block4Chunk0ParentPath_13_ok,
    tttLargeFiber30Block4Chunk0ParentPath_14_ok,
    tttLargeFiber30Block4Chunk0ParentPath_15_ok]

def tttLargeFiber30Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block4Chunk0SourcesCheck &&
    tttLargeFiber30Block4Chunk0RowsAudit &&
    tttLargeFiber30Block4Chunk0ParentMapAudit &&
    tttLargeFiber30Block4Chunk0ParentsAudit

theorem tttLargeFiber30Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber30Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block4Chunk0SourcesCheck_ok,
    tttLargeFiber30Block4Chunk0RowsAudit_ok,
    tttLargeFiber30Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber30Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
