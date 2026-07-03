import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 5 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block5Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block5Chunk1Sources : List Nat :=
  [   1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719,
   1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]

def tttLargeFiber30Row336 : TripleComponentParentRow :=
  tripleRow 1712 80 49 158 0 1 90 16
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

def tttLargeFiber30Row337 : TripleComponentParentRow :=
  tripleRow 1713 81 49 158 1 1 90 17
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

def tttLargeFiber30Row338 : TripleComponentParentRow :=
  tripleRow 1714 82 49 158 2 1 90 18
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

def tttLargeFiber30Row339 : TripleComponentParentRow :=
  tripleRow 1715 83 49 158 3 1 90 19
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

def tttLargeFiber30Row340 : TripleComponentParentRow :=
  tripleRow 1716 1704 49 158 48 49 157 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row341 : TripleComponentParentRow :=
  tripleRow 1717 1705 49 158 49 49 157 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row342 : TripleComponentParentRow :=
  tripleRow 1718 86 49 158 50 1 90 34
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

def tttLargeFiber30Row343 : TripleComponentParentRow :=
  tripleRow 1719 87 49 158 51 1 90 35
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

def tttLargeFiber30Row344 : TripleComponentParentRow :=
  tripleRow 1720 1703 49 159 8 49 156 167
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

def tttLargeFiber30Row345 : TripleComponentParentRow :=
  tripleRow 1721 1702 49 159 9 49 156 166
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

def tttLargeFiber30Row346 : TripleComponentParentRow :=
  tripleRow 1722 1700 49 159 10 49 156 164
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

def tttLargeFiber30Row347 : TripleComponentParentRow :=
  tripleRow 1723 1701 49 159 11 49 156 165
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

def tttLargeFiber30Row348 : TripleComponentParentRow :=
  tripleRow 1724 1696 49 159 56 49 156 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row349 : TripleComponentParentRow :=
  tripleRow 1725 1697 49 159 57 49 156 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row350 : TripleComponentParentRow :=
  tripleRow 1726 1698 49 159 58 49 156 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Row351 : TripleComponentParentRow :=
  tripleRow 1727 1699 49 159 59 49 156 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber30Block5Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row336
  , tttLargeFiber30Row337
  , tttLargeFiber30Row338
  , tttLargeFiber30Row339
  , tttLargeFiber30Row340
  , tttLargeFiber30Row341
  , tttLargeFiber30Row342
  , tttLargeFiber30Row343
  , tttLargeFiber30Row344
  , tttLargeFiber30Row345
  , tttLargeFiber30Row346
  , tttLargeFiber30Row347
  , tttLargeFiber30Row348
  , tttLargeFiber30Row349
  , tttLargeFiber30Row350
  , tttLargeFiber30Row351
  ]

def tttLargeFiber30Block5Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block5Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block5Chunk1ExpectedContains row.source &&
    tttLargeFiber30Block5Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block5Chunk1SourcesCheck : Bool :=
  (tttLargeFiber30Block5Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber30Block5Chunk1Sources

theorem tttLargeFiber30Block5Chunk1SourcesCheck_ok :
    tttLargeFiber30Block5Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber30Block5Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block5Chunk1RowValid
    (listGetD tttLargeFiber30Block5Chunk1Rows i default)

def tttLargeFiber30Block5Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block5Chunk1Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block5Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block5Chunk1Sources 0 0 == 1712
      && tttLargeFiber30ParentOf 1712 == 80
      && tttLargeFiber30ParentOf 80 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block5Chunk1Sources 1 0 == 1713
      && tttLargeFiber30ParentOf 1713 == 81
      && tttLargeFiber30ParentOf 81 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block5Chunk1Sources 2 0 == 1714
      && tttLargeFiber30ParentOf 1714 == 82
      && tttLargeFiber30ParentOf 82 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block5Chunk1Sources 3 0 == 1715
      && tttLargeFiber30ParentOf 1715 == 83
      && tttLargeFiber30ParentOf 83 == 19
      && tttLargeFiber30ParentOf 19 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block5Chunk1Sources 4 0 == 1716
      && tttLargeFiber30ParentOf 1716 == 1704
      && tttLargeFiber30ParentOf 1704 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block5Chunk1Sources 5 0 == 1717
      && tttLargeFiber30ParentOf 1717 == 1705
      && tttLargeFiber30ParentOf 1705 == 73
      && tttLargeFiber30ParentOf 73 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block5Chunk1Sources 6 0 == 1718
      && tttLargeFiber30ParentOf 1718 == 86
      && tttLargeFiber30ParentOf 86 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block5Chunk1Sources 7 0 == 1719
      && tttLargeFiber30ParentOf 1719 == 87
      && tttLargeFiber30ParentOf 87 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block5Chunk1Sources 8 0 == 1720
      && tttLargeFiber30ParentOf 1720 == 1703
      && tttLargeFiber30ParentOf 1703 == 71
      && tttLargeFiber30ParentOf 71 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block5Chunk1Sources 9 0 == 1721
      && tttLargeFiber30ParentOf 1721 == 1702
      && tttLargeFiber30ParentOf 1702 == 70
      && tttLargeFiber30ParentOf 70 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block5Chunk1Sources 10 0 == 1722
      && tttLargeFiber30ParentOf 1722 == 1700
      && tttLargeFiber30ParentOf 1700 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block5Chunk1Sources 11 0 == 1723
      && tttLargeFiber30ParentOf 1723 == 1701
      && tttLargeFiber30ParentOf 1701 == 1697
      && tttLargeFiber30ParentOf 1697 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block5Chunk1Sources 12 0 == 1724
      && tttLargeFiber30ParentOf 1724 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block5Chunk1Sources 13 0 == 1725
      && tttLargeFiber30ParentOf 1725 == 1697
      && tttLargeFiber30ParentOf 1697 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block5Chunk1Sources 14 0 == 1726
      && tttLargeFiber30ParentOf 1726 == 1698
      && tttLargeFiber30ParentOf 1698 == 66
      && tttLargeFiber30ParentOf 66 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block5Chunk1Sources 15 0 == 1727
      && tttLargeFiber30ParentOf 1727 == 1699
      && tttLargeFiber30ParentOf 1699 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block5Chunk1Row_0_ok :
    tttLargeFiber30Block5Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_1_ok :
    tttLargeFiber30Block5Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_2_ok :
    tttLargeFiber30Block5Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_3_ok :
    tttLargeFiber30Block5Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_4_ok :
    tttLargeFiber30Block5Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_5_ok :
    tttLargeFiber30Block5Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_6_ok :
    tttLargeFiber30Block5Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_7_ok :
    tttLargeFiber30Block5Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_8_ok :
    tttLargeFiber30Block5Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_9_ok :
    tttLargeFiber30Block5Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_10_ok :
    tttLargeFiber30Block5Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_11_ok :
    tttLargeFiber30Block5Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_12_ok :
    tttLargeFiber30Block5Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_13_ok :
    tttLargeFiber30Block5Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_14_ok :
    tttLargeFiber30Block5Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1Row_15_ok :
    tttLargeFiber30Block5Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_0_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_1_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_2_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_3_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_4_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_5_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_6_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_7_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_8_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_9_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_10_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_11_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_12_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_13_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_14_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentMap_15_ok :
    tttLargeFiber30Block5Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_0_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_1_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_2_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_3_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_4_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_5_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_6_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_7_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_8_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_9_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_10_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_11_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_12_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_13_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_14_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk1ParentPath_15_ok :
    tttLargeFiber30Block5Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block5Chunk1RowsAudit : Bool :=
  tttLargeFiber30Block5Chunk1RowCheck 0
    && tttLargeFiber30Block5Chunk1RowCheck 1
    && tttLargeFiber30Block5Chunk1RowCheck 2
    && tttLargeFiber30Block5Chunk1RowCheck 3
    && tttLargeFiber30Block5Chunk1RowCheck 4
    && tttLargeFiber30Block5Chunk1RowCheck 5
    && tttLargeFiber30Block5Chunk1RowCheck 6
    && tttLargeFiber30Block5Chunk1RowCheck 7
    && tttLargeFiber30Block5Chunk1RowCheck 8
    && tttLargeFiber30Block5Chunk1RowCheck 9
    && tttLargeFiber30Block5Chunk1RowCheck 10
    && tttLargeFiber30Block5Chunk1RowCheck 11
    && tttLargeFiber30Block5Chunk1RowCheck 12
    && tttLargeFiber30Block5Chunk1RowCheck 13
    && tttLargeFiber30Block5Chunk1RowCheck 14
    && tttLargeFiber30Block5Chunk1RowCheck 15

theorem tttLargeFiber30Block5Chunk1RowsAudit_ok :
    tttLargeFiber30Block5Chunk1RowsAudit = true := by
  simp [tttLargeFiber30Block5Chunk1RowsAudit,
    tttLargeFiber30Block5Chunk1Row_0_ok,
    tttLargeFiber30Block5Chunk1Row_1_ok,
    tttLargeFiber30Block5Chunk1Row_2_ok,
    tttLargeFiber30Block5Chunk1Row_3_ok,
    tttLargeFiber30Block5Chunk1Row_4_ok,
    tttLargeFiber30Block5Chunk1Row_5_ok,
    tttLargeFiber30Block5Chunk1Row_6_ok,
    tttLargeFiber30Block5Chunk1Row_7_ok,
    tttLargeFiber30Block5Chunk1Row_8_ok,
    tttLargeFiber30Block5Chunk1Row_9_ok,
    tttLargeFiber30Block5Chunk1Row_10_ok,
    tttLargeFiber30Block5Chunk1Row_11_ok,
    tttLargeFiber30Block5Chunk1Row_12_ok,
    tttLargeFiber30Block5Chunk1Row_13_ok,
    tttLargeFiber30Block5Chunk1Row_14_ok,
    tttLargeFiber30Block5Chunk1Row_15_ok]

def tttLargeFiber30Block5Chunk1ParentMapAudit : Bool :=
  tttLargeFiber30Block5Chunk1ParentMapCheck 0
    && tttLargeFiber30Block5Chunk1ParentMapCheck 1
    && tttLargeFiber30Block5Chunk1ParentMapCheck 2
    && tttLargeFiber30Block5Chunk1ParentMapCheck 3
    && tttLargeFiber30Block5Chunk1ParentMapCheck 4
    && tttLargeFiber30Block5Chunk1ParentMapCheck 5
    && tttLargeFiber30Block5Chunk1ParentMapCheck 6
    && tttLargeFiber30Block5Chunk1ParentMapCheck 7
    && tttLargeFiber30Block5Chunk1ParentMapCheck 8
    && tttLargeFiber30Block5Chunk1ParentMapCheck 9
    && tttLargeFiber30Block5Chunk1ParentMapCheck 10
    && tttLargeFiber30Block5Chunk1ParentMapCheck 11
    && tttLargeFiber30Block5Chunk1ParentMapCheck 12
    && tttLargeFiber30Block5Chunk1ParentMapCheck 13
    && tttLargeFiber30Block5Chunk1ParentMapCheck 14
    && tttLargeFiber30Block5Chunk1ParentMapCheck 15

theorem tttLargeFiber30Block5Chunk1ParentMapAudit_ok :
    tttLargeFiber30Block5Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber30Block5Chunk1ParentMapAudit,
    tttLargeFiber30Block5Chunk1ParentMap_0_ok,
    tttLargeFiber30Block5Chunk1ParentMap_1_ok,
    tttLargeFiber30Block5Chunk1ParentMap_2_ok,
    tttLargeFiber30Block5Chunk1ParentMap_3_ok,
    tttLargeFiber30Block5Chunk1ParentMap_4_ok,
    tttLargeFiber30Block5Chunk1ParentMap_5_ok,
    tttLargeFiber30Block5Chunk1ParentMap_6_ok,
    tttLargeFiber30Block5Chunk1ParentMap_7_ok,
    tttLargeFiber30Block5Chunk1ParentMap_8_ok,
    tttLargeFiber30Block5Chunk1ParentMap_9_ok,
    tttLargeFiber30Block5Chunk1ParentMap_10_ok,
    tttLargeFiber30Block5Chunk1ParentMap_11_ok,
    tttLargeFiber30Block5Chunk1ParentMap_12_ok,
    tttLargeFiber30Block5Chunk1ParentMap_13_ok,
    tttLargeFiber30Block5Chunk1ParentMap_14_ok,
    tttLargeFiber30Block5Chunk1ParentMap_15_ok]

def tttLargeFiber30Block5Chunk1ParentsAudit : Bool :=
  tttLargeFiber30Block5Chunk1ParentPathCheck 0
    && tttLargeFiber30Block5Chunk1ParentPathCheck 1
    && tttLargeFiber30Block5Chunk1ParentPathCheck 2
    && tttLargeFiber30Block5Chunk1ParentPathCheck 3
    && tttLargeFiber30Block5Chunk1ParentPathCheck 4
    && tttLargeFiber30Block5Chunk1ParentPathCheck 5
    && tttLargeFiber30Block5Chunk1ParentPathCheck 6
    && tttLargeFiber30Block5Chunk1ParentPathCheck 7
    && tttLargeFiber30Block5Chunk1ParentPathCheck 8
    && tttLargeFiber30Block5Chunk1ParentPathCheck 9
    && tttLargeFiber30Block5Chunk1ParentPathCheck 10
    && tttLargeFiber30Block5Chunk1ParentPathCheck 11
    && tttLargeFiber30Block5Chunk1ParentPathCheck 12
    && tttLargeFiber30Block5Chunk1ParentPathCheck 13
    && tttLargeFiber30Block5Chunk1ParentPathCheck 14
    && tttLargeFiber30Block5Chunk1ParentPathCheck 15

theorem tttLargeFiber30Block5Chunk1ParentsAudit_ok :
    tttLargeFiber30Block5Chunk1ParentsAudit = true := by
  simp [tttLargeFiber30Block5Chunk1ParentsAudit,
    tttLargeFiber30Block5Chunk1ParentPath_0_ok,
    tttLargeFiber30Block5Chunk1ParentPath_1_ok,
    tttLargeFiber30Block5Chunk1ParentPath_2_ok,
    tttLargeFiber30Block5Chunk1ParentPath_3_ok,
    tttLargeFiber30Block5Chunk1ParentPath_4_ok,
    tttLargeFiber30Block5Chunk1ParentPath_5_ok,
    tttLargeFiber30Block5Chunk1ParentPath_6_ok,
    tttLargeFiber30Block5Chunk1ParentPath_7_ok,
    tttLargeFiber30Block5Chunk1ParentPath_8_ok,
    tttLargeFiber30Block5Chunk1ParentPath_9_ok,
    tttLargeFiber30Block5Chunk1ParentPath_10_ok,
    tttLargeFiber30Block5Chunk1ParentPath_11_ok,
    tttLargeFiber30Block5Chunk1ParentPath_12_ok,
    tttLargeFiber30Block5Chunk1ParentPath_13_ok,
    tttLargeFiber30Block5Chunk1ParentPath_14_ok,
    tttLargeFiber30Block5Chunk1ParentPath_15_ok]

def tttLargeFiber30Block5Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block5Chunk1SourcesCheck &&
    tttLargeFiber30Block5Chunk1RowsAudit &&
    tttLargeFiber30Block5Chunk1ParentMapAudit &&
    tttLargeFiber30Block5Chunk1ParentsAudit

theorem tttLargeFiber30Block5Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber30Block5Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block5Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block5Chunk1SourcesCheck_ok,
    tttLargeFiber30Block5Chunk1RowsAudit_ok,
    tttLargeFiber30Block5Chunk1ParentMapAudit_ok,
    tttLargeFiber30Block5Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block5Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
