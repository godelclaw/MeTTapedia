import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 4 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block4Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block4Chunk1Sources : List Nat :=
  [   1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655,
   1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]

def tttLargeFiber30Row272 : TripleComponentParentRow :=
  tripleRow 1648 16 48 150 0 0 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row273 : TripleComponentParentRow :=
  tripleRow 1649 17 48 150 1 0 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row274 : TripleComponentParentRow :=
  tripleRow 1650 18 48 150 2 0 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row275 : TripleComponentParentRow :=
  tripleRow 1651 19 48 150 3 0 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row276 : TripleComponentParentRow :=
  tripleRow 1652 1640 48 150 48 48 149 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row277 : TripleComponentParentRow :=
  tripleRow 1653 1641 48 150 49 48 149 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row278 : TripleComponentParentRow :=
  tripleRow 1654 22 48 150 50 0 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row279 : TripleComponentParentRow :=
  tripleRow 1655 23 48 150 51 0 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row280 : TripleComponentParentRow :=
  tripleRow 1656 1639 48 151 8 48 148 167
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row281 : TripleComponentParentRow :=
  tripleRow 1657 1638 48 151 9 48 148 166
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row282 : TripleComponentParentRow :=
  tripleRow 1658 1636 48 151 10 48 148 164
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row283 : TripleComponentParentRow :=
  tripleRow 1659 1637 48 151 11 48 148 165
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row284 : TripleComponentParentRow :=
  tripleRow 1660 1632 48 151 56 48 148 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row285 : TripleComponentParentRow :=
  tripleRow 1661 1633 48 151 57 48 148 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row286 : TripleComponentParentRow :=
  tripleRow 1662 1634 48 151 58 48 148 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row287 : TripleComponentParentRow :=
  tripleRow 1663 1635 48 151 59 48 148 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Block4Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row272
  , tttLargeFiber30Row273
  , tttLargeFiber30Row274
  , tttLargeFiber30Row275
  , tttLargeFiber30Row276
  , tttLargeFiber30Row277
  , tttLargeFiber30Row278
  , tttLargeFiber30Row279
  , tttLargeFiber30Row280
  , tttLargeFiber30Row281
  , tttLargeFiber30Row282
  , tttLargeFiber30Row283
  , tttLargeFiber30Row284
  , tttLargeFiber30Row285
  , tttLargeFiber30Row286
  , tttLargeFiber30Row287
  ]

def tttLargeFiber30Block4Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block4Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block4Chunk1ExpectedContains row.source &&
    tttLargeFiber30Block4Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block4Chunk1SourcesCheck : Bool :=
  (tttLargeFiber30Block4Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber30Block4Chunk1Sources

theorem tttLargeFiber30Block4Chunk1SourcesCheck_ok :
    tttLargeFiber30Block4Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber30Block4Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block4Chunk1RowValid
    (listGetD tttLargeFiber30Block4Chunk1Rows i default)

def tttLargeFiber30Block4Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block4Chunk1Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block4Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block4Chunk1Sources 0 0 == 1648
      && tttLargeFiber30ParentOf 1648 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block4Chunk1Sources 1 0 == 1649
      && tttLargeFiber30ParentOf 1649 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block4Chunk1Sources 2 0 == 1650
      && tttLargeFiber30ParentOf 1650 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block4Chunk1Sources 3 0 == 1651
      && tttLargeFiber30ParentOf 1651 == 19
      && tttLargeFiber30ParentOf 19 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block4Chunk1Sources 4 0 == 1652
      && tttLargeFiber30ParentOf 1652 == 1640
      && tttLargeFiber30ParentOf 1640 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block4Chunk1Sources 5 0 == 1653
      && tttLargeFiber30ParentOf 1653 == 1641
      && tttLargeFiber30ParentOf 1641 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block4Chunk1Sources 6 0 == 1654
      && tttLargeFiber30ParentOf 1654 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block4Chunk1Sources 7 0 == 1655
      && tttLargeFiber30ParentOf 1655 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block4Chunk1Sources 8 0 == 1656
      && tttLargeFiber30ParentOf 1656 == 1639
      && tttLargeFiber30ParentOf 1639 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block4Chunk1Sources 9 0 == 1657
      && tttLargeFiber30ParentOf 1657 == 1638
      && tttLargeFiber30ParentOf 1638 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block4Chunk1Sources 10 0 == 1658
      && tttLargeFiber30ParentOf 1658 == 1636
      && tttLargeFiber30ParentOf 1636 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block4Chunk1Sources 11 0 == 1659
      && tttLargeFiber30ParentOf 1659 == 1637
      && tttLargeFiber30ParentOf 1637 == 1633
      && tttLargeFiber30ParentOf 1633 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block4Chunk1Sources 12 0 == 1660
      && tttLargeFiber30ParentOf 1660 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block4Chunk1Sources 13 0 == 1661
      && tttLargeFiber30ParentOf 1661 == 1633
      && tttLargeFiber30ParentOf 1633 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block4Chunk1Sources 14 0 == 1662
      && tttLargeFiber30ParentOf 1662 == 1634
      && tttLargeFiber30ParentOf 1634 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block4Chunk1Sources 15 0 == 1663
      && tttLargeFiber30ParentOf 1663 == 1635
      && tttLargeFiber30ParentOf 1635 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block4Chunk1Row_0_ok :
    tttLargeFiber30Block4Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_1_ok :
    tttLargeFiber30Block4Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_2_ok :
    tttLargeFiber30Block4Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_3_ok :
    tttLargeFiber30Block4Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_4_ok :
    tttLargeFiber30Block4Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_5_ok :
    tttLargeFiber30Block4Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_6_ok :
    tttLargeFiber30Block4Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_7_ok :
    tttLargeFiber30Block4Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_8_ok :
    tttLargeFiber30Block4Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_9_ok :
    tttLargeFiber30Block4Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_10_ok :
    tttLargeFiber30Block4Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_11_ok :
    tttLargeFiber30Block4Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_12_ok :
    tttLargeFiber30Block4Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_13_ok :
    tttLargeFiber30Block4Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_14_ok :
    tttLargeFiber30Block4Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1Row_15_ok :
    tttLargeFiber30Block4Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_0_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_1_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_2_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_3_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_4_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_5_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_6_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_7_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_8_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_9_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_10_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_11_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_12_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_13_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_14_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentMap_15_ok :
    tttLargeFiber30Block4Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_0_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_1_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_2_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_3_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_4_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_5_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_6_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_7_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_8_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_9_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_10_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_11_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_12_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_13_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_14_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk1ParentPath_15_ok :
    tttLargeFiber30Block4Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block4Chunk1RowsAudit : Bool :=
  tttLargeFiber30Block4Chunk1RowCheck 0
    && tttLargeFiber30Block4Chunk1RowCheck 1
    && tttLargeFiber30Block4Chunk1RowCheck 2
    && tttLargeFiber30Block4Chunk1RowCheck 3
    && tttLargeFiber30Block4Chunk1RowCheck 4
    && tttLargeFiber30Block4Chunk1RowCheck 5
    && tttLargeFiber30Block4Chunk1RowCheck 6
    && tttLargeFiber30Block4Chunk1RowCheck 7
    && tttLargeFiber30Block4Chunk1RowCheck 8
    && tttLargeFiber30Block4Chunk1RowCheck 9
    && tttLargeFiber30Block4Chunk1RowCheck 10
    && tttLargeFiber30Block4Chunk1RowCheck 11
    && tttLargeFiber30Block4Chunk1RowCheck 12
    && tttLargeFiber30Block4Chunk1RowCheck 13
    && tttLargeFiber30Block4Chunk1RowCheck 14
    && tttLargeFiber30Block4Chunk1RowCheck 15

theorem tttLargeFiber30Block4Chunk1RowsAudit_ok :
    tttLargeFiber30Block4Chunk1RowsAudit = true := by
  simp [tttLargeFiber30Block4Chunk1RowsAudit,
    tttLargeFiber30Block4Chunk1Row_0_ok,
    tttLargeFiber30Block4Chunk1Row_1_ok,
    tttLargeFiber30Block4Chunk1Row_2_ok,
    tttLargeFiber30Block4Chunk1Row_3_ok,
    tttLargeFiber30Block4Chunk1Row_4_ok,
    tttLargeFiber30Block4Chunk1Row_5_ok,
    tttLargeFiber30Block4Chunk1Row_6_ok,
    tttLargeFiber30Block4Chunk1Row_7_ok,
    tttLargeFiber30Block4Chunk1Row_8_ok,
    tttLargeFiber30Block4Chunk1Row_9_ok,
    tttLargeFiber30Block4Chunk1Row_10_ok,
    tttLargeFiber30Block4Chunk1Row_11_ok,
    tttLargeFiber30Block4Chunk1Row_12_ok,
    tttLargeFiber30Block4Chunk1Row_13_ok,
    tttLargeFiber30Block4Chunk1Row_14_ok,
    tttLargeFiber30Block4Chunk1Row_15_ok]

def tttLargeFiber30Block4Chunk1ParentMapAudit : Bool :=
  tttLargeFiber30Block4Chunk1ParentMapCheck 0
    && tttLargeFiber30Block4Chunk1ParentMapCheck 1
    && tttLargeFiber30Block4Chunk1ParentMapCheck 2
    && tttLargeFiber30Block4Chunk1ParentMapCheck 3
    && tttLargeFiber30Block4Chunk1ParentMapCheck 4
    && tttLargeFiber30Block4Chunk1ParentMapCheck 5
    && tttLargeFiber30Block4Chunk1ParentMapCheck 6
    && tttLargeFiber30Block4Chunk1ParentMapCheck 7
    && tttLargeFiber30Block4Chunk1ParentMapCheck 8
    && tttLargeFiber30Block4Chunk1ParentMapCheck 9
    && tttLargeFiber30Block4Chunk1ParentMapCheck 10
    && tttLargeFiber30Block4Chunk1ParentMapCheck 11
    && tttLargeFiber30Block4Chunk1ParentMapCheck 12
    && tttLargeFiber30Block4Chunk1ParentMapCheck 13
    && tttLargeFiber30Block4Chunk1ParentMapCheck 14
    && tttLargeFiber30Block4Chunk1ParentMapCheck 15

theorem tttLargeFiber30Block4Chunk1ParentMapAudit_ok :
    tttLargeFiber30Block4Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber30Block4Chunk1ParentMapAudit,
    tttLargeFiber30Block4Chunk1ParentMap_0_ok,
    tttLargeFiber30Block4Chunk1ParentMap_1_ok,
    tttLargeFiber30Block4Chunk1ParentMap_2_ok,
    tttLargeFiber30Block4Chunk1ParentMap_3_ok,
    tttLargeFiber30Block4Chunk1ParentMap_4_ok,
    tttLargeFiber30Block4Chunk1ParentMap_5_ok,
    tttLargeFiber30Block4Chunk1ParentMap_6_ok,
    tttLargeFiber30Block4Chunk1ParentMap_7_ok,
    tttLargeFiber30Block4Chunk1ParentMap_8_ok,
    tttLargeFiber30Block4Chunk1ParentMap_9_ok,
    tttLargeFiber30Block4Chunk1ParentMap_10_ok,
    tttLargeFiber30Block4Chunk1ParentMap_11_ok,
    tttLargeFiber30Block4Chunk1ParentMap_12_ok,
    tttLargeFiber30Block4Chunk1ParentMap_13_ok,
    tttLargeFiber30Block4Chunk1ParentMap_14_ok,
    tttLargeFiber30Block4Chunk1ParentMap_15_ok]

def tttLargeFiber30Block4Chunk1ParentsAudit : Bool :=
  tttLargeFiber30Block4Chunk1ParentPathCheck 0
    && tttLargeFiber30Block4Chunk1ParentPathCheck 1
    && tttLargeFiber30Block4Chunk1ParentPathCheck 2
    && tttLargeFiber30Block4Chunk1ParentPathCheck 3
    && tttLargeFiber30Block4Chunk1ParentPathCheck 4
    && tttLargeFiber30Block4Chunk1ParentPathCheck 5
    && tttLargeFiber30Block4Chunk1ParentPathCheck 6
    && tttLargeFiber30Block4Chunk1ParentPathCheck 7
    && tttLargeFiber30Block4Chunk1ParentPathCheck 8
    && tttLargeFiber30Block4Chunk1ParentPathCheck 9
    && tttLargeFiber30Block4Chunk1ParentPathCheck 10
    && tttLargeFiber30Block4Chunk1ParentPathCheck 11
    && tttLargeFiber30Block4Chunk1ParentPathCheck 12
    && tttLargeFiber30Block4Chunk1ParentPathCheck 13
    && tttLargeFiber30Block4Chunk1ParentPathCheck 14
    && tttLargeFiber30Block4Chunk1ParentPathCheck 15

theorem tttLargeFiber30Block4Chunk1ParentsAudit_ok :
    tttLargeFiber30Block4Chunk1ParentsAudit = true := by
  simp [tttLargeFiber30Block4Chunk1ParentsAudit,
    tttLargeFiber30Block4Chunk1ParentPath_0_ok,
    tttLargeFiber30Block4Chunk1ParentPath_1_ok,
    tttLargeFiber30Block4Chunk1ParentPath_2_ok,
    tttLargeFiber30Block4Chunk1ParentPath_3_ok,
    tttLargeFiber30Block4Chunk1ParentPath_4_ok,
    tttLargeFiber30Block4Chunk1ParentPath_5_ok,
    tttLargeFiber30Block4Chunk1ParentPath_6_ok,
    tttLargeFiber30Block4Chunk1ParentPath_7_ok,
    tttLargeFiber30Block4Chunk1ParentPath_8_ok,
    tttLargeFiber30Block4Chunk1ParentPath_9_ok,
    tttLargeFiber30Block4Chunk1ParentPath_10_ok,
    tttLargeFiber30Block4Chunk1ParentPath_11_ok,
    tttLargeFiber30Block4Chunk1ParentPath_12_ok,
    tttLargeFiber30Block4Chunk1ParentPath_13_ok,
    tttLargeFiber30Block4Chunk1ParentPath_14_ok,
    tttLargeFiber30Block4Chunk1ParentPath_15_ok]

def tttLargeFiber30Block4Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block4Chunk1SourcesCheck &&
    tttLargeFiber30Block4Chunk1RowsAudit &&
    tttLargeFiber30Block4Chunk1ParentMapAudit &&
    tttLargeFiber30Block4Chunk1ParentsAudit

theorem tttLargeFiber30Block4Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber30Block4Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block4Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block4Chunk1SourcesCheck_ok,
    tttLargeFiber30Block4Chunk1RowsAudit_ok,
    tttLargeFiber30Block4Chunk1ParentMapAudit_ok,
    tttLargeFiber30Block4Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block4Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
