import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 4 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block4Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block4Chunk3Sources : List Nat :=
  [   1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687,
   1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]

def tttLargeFiber30Row304 : TripleComponentParentRow :=
  tripleRow 1680 48 48 166 64 0 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row305 : TripleComponentParentRow :=
  tripleRow 1681 49 48 166 65 0 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row306 : TripleComponentParentRow :=
  tripleRow 1682 50 48 166 66 0 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row307 : TripleComponentParentRow :=
  tripleRow 1683 1667 48 166 67 48 164 135
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
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

def tttLargeFiber30Row308 : TripleComponentParentRow :=
  tripleRow 1684 1652 48 166 116 48 150 48
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber30Row309 : TripleComponentParentRow :=
  tripleRow 1685 1653 48 166 117 48 150 49
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber30Row310 : TripleComponentParentRow :=
  tripleRow 1686 54 48 166 118 0 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row311 : TripleComponentParentRow :=
  tripleRow 1687 55 48 166 119 0 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row312 : TripleComponentParentRow :=
  tripleRow 1688 56 48 167 72 0 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row313 : TripleComponentParentRow :=
  tripleRow 1689 57 48 167 73 0 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row314 : TripleComponentParentRow :=
  tripleRow 1690 58 48 167 74 0 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row315 : TripleComponentParentRow :=
  tripleRow 1691 59 48 167 75 0 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row316 : TripleComponentParentRow :=
  tripleRow 1692 1660 48 167 124 48 151 56
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber30Row317 : TripleComponentParentRow :=
  tripleRow 1693 1661 48 167 125 48 151 57
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber30Row318 : TripleComponentParentRow :=
  tripleRow 1694 62 48 167 126 0 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row319 : TripleComponentParentRow :=
  tripleRow 1695 63 48 167 127 0 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Block4Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row304
  , tttLargeFiber30Row305
  , tttLargeFiber30Row306
  , tttLargeFiber30Row307
  , tttLargeFiber30Row308
  , tttLargeFiber30Row309
  , tttLargeFiber30Row310
  , tttLargeFiber30Row311
  , tttLargeFiber30Row312
  , tttLargeFiber30Row313
  , tttLargeFiber30Row314
  , tttLargeFiber30Row315
  , tttLargeFiber30Row316
  , tttLargeFiber30Row317
  , tttLargeFiber30Row318
  , tttLargeFiber30Row319
  ]

def tttLargeFiber30Block4Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block4Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block4Chunk3ExpectedContains row.source &&
    tttLargeFiber30Block4Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block4Chunk3SourcesCheck : Bool :=
  (tttLargeFiber30Block4Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber30Block4Chunk3Sources

theorem tttLargeFiber30Block4Chunk3SourcesCheck_ok :
    tttLargeFiber30Block4Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber30Block4Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block4Chunk3RowValid
    (listGetD tttLargeFiber30Block4Chunk3Rows i default)

def tttLargeFiber30Block4Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block4Chunk3Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block4Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block4Chunk3Sources 0 0 == 1680
      && tttLargeFiber30ParentOf 1680 == 48
      && tttLargeFiber30ParentOf 48 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block4Chunk3Sources 1 0 == 1681
      && tttLargeFiber30ParentOf 1681 == 49
      && tttLargeFiber30ParentOf 49 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block4Chunk3Sources 2 0 == 1682
      && tttLargeFiber30ParentOf 1682 == 50
      && tttLargeFiber30ParentOf 50 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block4Chunk3Sources 3 0 == 1683
      && tttLargeFiber30ParentOf 1683 == 1667
      && tttLargeFiber30ParentOf 1667 == 1635
      && tttLargeFiber30ParentOf 1635 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block4Chunk3Sources 4 0 == 1684
      && tttLargeFiber30ParentOf 1684 == 1652
      && tttLargeFiber30ParentOf 1652 == 1640
      && tttLargeFiber30ParentOf 1640 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block4Chunk3Sources 5 0 == 1685
      && tttLargeFiber30ParentOf 1685 == 1653
      && tttLargeFiber30ParentOf 1653 == 1641
      && tttLargeFiber30ParentOf 1641 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block4Chunk3Sources 6 0 == 1686
      && tttLargeFiber30ParentOf 1686 == 54
      && tttLargeFiber30ParentOf 54 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block4Chunk3Sources 7 0 == 1687
      && tttLargeFiber30ParentOf 1687 == 55
      && tttLargeFiber30ParentOf 55 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block4Chunk3Sources 8 0 == 1688
      && tttLargeFiber30ParentOf 1688 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block4Chunk3Sources 9 0 == 1689
      && tttLargeFiber30ParentOf 1689 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block4Chunk3Sources 10 0 == 1690
      && tttLargeFiber30ParentOf 1690 == 58
      && tttLargeFiber30ParentOf 58 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block4Chunk3Sources 11 0 == 1691
      && tttLargeFiber30ParentOf 1691 == 59
      && tttLargeFiber30ParentOf 59 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block4Chunk3Sources 12 0 == 1692
      && tttLargeFiber30ParentOf 1692 == 1660
      && tttLargeFiber30ParentOf 1660 == 1632
      && tttLargeFiber30ParentOf 1632 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block4Chunk3Sources 13 0 == 1693
      && tttLargeFiber30ParentOf 1693 == 1661
      && tttLargeFiber30ParentOf 1661 == 1633
      && tttLargeFiber30ParentOf 1633 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block4Chunk3Sources 14 0 == 1694
      && tttLargeFiber30ParentOf 1694 == 62
      && tttLargeFiber30ParentOf 62 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block4Chunk3Sources 15 0 == 1695
      && tttLargeFiber30ParentOf 1695 == 63
      && tttLargeFiber30ParentOf 63 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block4Chunk3Row_0_ok :
    tttLargeFiber30Block4Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_1_ok :
    tttLargeFiber30Block4Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_2_ok :
    tttLargeFiber30Block4Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_3_ok :
    tttLargeFiber30Block4Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_4_ok :
    tttLargeFiber30Block4Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_5_ok :
    tttLargeFiber30Block4Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_6_ok :
    tttLargeFiber30Block4Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_7_ok :
    tttLargeFiber30Block4Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_8_ok :
    tttLargeFiber30Block4Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_9_ok :
    tttLargeFiber30Block4Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_10_ok :
    tttLargeFiber30Block4Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_11_ok :
    tttLargeFiber30Block4Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_12_ok :
    tttLargeFiber30Block4Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_13_ok :
    tttLargeFiber30Block4Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_14_ok :
    tttLargeFiber30Block4Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3Row_15_ok :
    tttLargeFiber30Block4Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_0_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_1_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_2_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_3_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_4_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_5_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_6_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_7_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_8_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_9_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_10_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_11_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_12_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_13_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_14_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentMap_15_ok :
    tttLargeFiber30Block4Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_0_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_1_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_2_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_3_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_4_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_5_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_6_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_7_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_8_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_9_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_10_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_11_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_12_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_13_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_14_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block4Chunk3ParentPath_15_ok :
    tttLargeFiber30Block4Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block4Chunk3RowsAudit : Bool :=
  tttLargeFiber30Block4Chunk3RowCheck 0
    && tttLargeFiber30Block4Chunk3RowCheck 1
    && tttLargeFiber30Block4Chunk3RowCheck 2
    && tttLargeFiber30Block4Chunk3RowCheck 3
    && tttLargeFiber30Block4Chunk3RowCheck 4
    && tttLargeFiber30Block4Chunk3RowCheck 5
    && tttLargeFiber30Block4Chunk3RowCheck 6
    && tttLargeFiber30Block4Chunk3RowCheck 7
    && tttLargeFiber30Block4Chunk3RowCheck 8
    && tttLargeFiber30Block4Chunk3RowCheck 9
    && tttLargeFiber30Block4Chunk3RowCheck 10
    && tttLargeFiber30Block4Chunk3RowCheck 11
    && tttLargeFiber30Block4Chunk3RowCheck 12
    && tttLargeFiber30Block4Chunk3RowCheck 13
    && tttLargeFiber30Block4Chunk3RowCheck 14
    && tttLargeFiber30Block4Chunk3RowCheck 15

theorem tttLargeFiber30Block4Chunk3RowsAudit_ok :
    tttLargeFiber30Block4Chunk3RowsAudit = true := by
  simp [tttLargeFiber30Block4Chunk3RowsAudit,
    tttLargeFiber30Block4Chunk3Row_0_ok,
    tttLargeFiber30Block4Chunk3Row_1_ok,
    tttLargeFiber30Block4Chunk3Row_2_ok,
    tttLargeFiber30Block4Chunk3Row_3_ok,
    tttLargeFiber30Block4Chunk3Row_4_ok,
    tttLargeFiber30Block4Chunk3Row_5_ok,
    tttLargeFiber30Block4Chunk3Row_6_ok,
    tttLargeFiber30Block4Chunk3Row_7_ok,
    tttLargeFiber30Block4Chunk3Row_8_ok,
    tttLargeFiber30Block4Chunk3Row_9_ok,
    tttLargeFiber30Block4Chunk3Row_10_ok,
    tttLargeFiber30Block4Chunk3Row_11_ok,
    tttLargeFiber30Block4Chunk3Row_12_ok,
    tttLargeFiber30Block4Chunk3Row_13_ok,
    tttLargeFiber30Block4Chunk3Row_14_ok,
    tttLargeFiber30Block4Chunk3Row_15_ok]

def tttLargeFiber30Block4Chunk3ParentMapAudit : Bool :=
  tttLargeFiber30Block4Chunk3ParentMapCheck 0
    && tttLargeFiber30Block4Chunk3ParentMapCheck 1
    && tttLargeFiber30Block4Chunk3ParentMapCheck 2
    && tttLargeFiber30Block4Chunk3ParentMapCheck 3
    && tttLargeFiber30Block4Chunk3ParentMapCheck 4
    && tttLargeFiber30Block4Chunk3ParentMapCheck 5
    && tttLargeFiber30Block4Chunk3ParentMapCheck 6
    && tttLargeFiber30Block4Chunk3ParentMapCheck 7
    && tttLargeFiber30Block4Chunk3ParentMapCheck 8
    && tttLargeFiber30Block4Chunk3ParentMapCheck 9
    && tttLargeFiber30Block4Chunk3ParentMapCheck 10
    && tttLargeFiber30Block4Chunk3ParentMapCheck 11
    && tttLargeFiber30Block4Chunk3ParentMapCheck 12
    && tttLargeFiber30Block4Chunk3ParentMapCheck 13
    && tttLargeFiber30Block4Chunk3ParentMapCheck 14
    && tttLargeFiber30Block4Chunk3ParentMapCheck 15

theorem tttLargeFiber30Block4Chunk3ParentMapAudit_ok :
    tttLargeFiber30Block4Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber30Block4Chunk3ParentMapAudit,
    tttLargeFiber30Block4Chunk3ParentMap_0_ok,
    tttLargeFiber30Block4Chunk3ParentMap_1_ok,
    tttLargeFiber30Block4Chunk3ParentMap_2_ok,
    tttLargeFiber30Block4Chunk3ParentMap_3_ok,
    tttLargeFiber30Block4Chunk3ParentMap_4_ok,
    tttLargeFiber30Block4Chunk3ParentMap_5_ok,
    tttLargeFiber30Block4Chunk3ParentMap_6_ok,
    tttLargeFiber30Block4Chunk3ParentMap_7_ok,
    tttLargeFiber30Block4Chunk3ParentMap_8_ok,
    tttLargeFiber30Block4Chunk3ParentMap_9_ok,
    tttLargeFiber30Block4Chunk3ParentMap_10_ok,
    tttLargeFiber30Block4Chunk3ParentMap_11_ok,
    tttLargeFiber30Block4Chunk3ParentMap_12_ok,
    tttLargeFiber30Block4Chunk3ParentMap_13_ok,
    tttLargeFiber30Block4Chunk3ParentMap_14_ok,
    tttLargeFiber30Block4Chunk3ParentMap_15_ok]

def tttLargeFiber30Block4Chunk3ParentsAudit : Bool :=
  tttLargeFiber30Block4Chunk3ParentPathCheck 0
    && tttLargeFiber30Block4Chunk3ParentPathCheck 1
    && tttLargeFiber30Block4Chunk3ParentPathCheck 2
    && tttLargeFiber30Block4Chunk3ParentPathCheck 3
    && tttLargeFiber30Block4Chunk3ParentPathCheck 4
    && tttLargeFiber30Block4Chunk3ParentPathCheck 5
    && tttLargeFiber30Block4Chunk3ParentPathCheck 6
    && tttLargeFiber30Block4Chunk3ParentPathCheck 7
    && tttLargeFiber30Block4Chunk3ParentPathCheck 8
    && tttLargeFiber30Block4Chunk3ParentPathCheck 9
    && tttLargeFiber30Block4Chunk3ParentPathCheck 10
    && tttLargeFiber30Block4Chunk3ParentPathCheck 11
    && tttLargeFiber30Block4Chunk3ParentPathCheck 12
    && tttLargeFiber30Block4Chunk3ParentPathCheck 13
    && tttLargeFiber30Block4Chunk3ParentPathCheck 14
    && tttLargeFiber30Block4Chunk3ParentPathCheck 15

theorem tttLargeFiber30Block4Chunk3ParentsAudit_ok :
    tttLargeFiber30Block4Chunk3ParentsAudit = true := by
  simp [tttLargeFiber30Block4Chunk3ParentsAudit,
    tttLargeFiber30Block4Chunk3ParentPath_0_ok,
    tttLargeFiber30Block4Chunk3ParentPath_1_ok,
    tttLargeFiber30Block4Chunk3ParentPath_2_ok,
    tttLargeFiber30Block4Chunk3ParentPath_3_ok,
    tttLargeFiber30Block4Chunk3ParentPath_4_ok,
    tttLargeFiber30Block4Chunk3ParentPath_5_ok,
    tttLargeFiber30Block4Chunk3ParentPath_6_ok,
    tttLargeFiber30Block4Chunk3ParentPath_7_ok,
    tttLargeFiber30Block4Chunk3ParentPath_8_ok,
    tttLargeFiber30Block4Chunk3ParentPath_9_ok,
    tttLargeFiber30Block4Chunk3ParentPath_10_ok,
    tttLargeFiber30Block4Chunk3ParentPath_11_ok,
    tttLargeFiber30Block4Chunk3ParentPath_12_ok,
    tttLargeFiber30Block4Chunk3ParentPath_13_ok,
    tttLargeFiber30Block4Chunk3ParentPath_14_ok,
    tttLargeFiber30Block4Chunk3ParentPath_15_ok]

def tttLargeFiber30Block4Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block4Chunk3SourcesCheck &&
    tttLargeFiber30Block4Chunk3RowsAudit &&
    tttLargeFiber30Block4Chunk3ParentMapAudit &&
    tttLargeFiber30Block4Chunk3ParentsAudit

theorem tttLargeFiber30Block4Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber30Block4Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block4Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block4Chunk3SourcesCheck_ok,
    tttLargeFiber30Block4Chunk3RowsAudit_ok,
    tttLargeFiber30Block4Chunk3ParentMapAudit_ok,
    tttLargeFiber30Block4Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block4Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
