import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 5 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block5Chunk3Sources : List Nat :=
  [   1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751,
   1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]

def tttLargeFiber30Row368 : TripleComponentParentRow :=
  tripleRow 1744 112 49 174 64 1 110 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row369 : TripleComponentParentRow :=
  tripleRow 1745 113 49 174 65 1 110 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row370 : TripleComponentParentRow :=
  tripleRow 1746 114 49 174 66 1 110 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row371 : TripleComponentParentRow :=
  tripleRow 1747 1731 49 174 67 49 172 135
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

def tttLargeFiber30Row372 : TripleComponentParentRow :=
  tripleRow 1748 1716 49 174 116 49 158 48
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

def tttLargeFiber30Row373 : TripleComponentParentRow :=
  tripleRow 1749 1717 49 174 117 49 158 49
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

def tttLargeFiber30Row374 : TripleComponentParentRow :=
  tripleRow 1750 118 49 174 118 1 110 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row375 : TripleComponentParentRow :=
  tripleRow 1751 119 49 174 119 1 110 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row376 : TripleComponentParentRow :=
  tripleRow 1752 120 49 175 72 1 111 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row377 : TripleComponentParentRow :=
  tripleRow 1753 121 49 175 73 1 111 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row378 : TripleComponentParentRow :=
  tripleRow 1754 122 49 175 74 1 111 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row379 : TripleComponentParentRow :=
  tripleRow 1755 123 49 175 75 1 111 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row380 : TripleComponentParentRow :=
  tripleRow 1756 1724 49 175 124 49 159 56
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

def tttLargeFiber30Row381 : TripleComponentParentRow :=
  tripleRow 1757 1725 49 175 125 49 159 57
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

def tttLargeFiber30Row382 : TripleComponentParentRow :=
  tripleRow 1758 126 49 175 126 1 111 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Row383 : TripleComponentParentRow :=
  tripleRow 1759 127 49 175 127 1 111 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber30Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row368
  , tttLargeFiber30Row369
  , tttLargeFiber30Row370
  , tttLargeFiber30Row371
  , tttLargeFiber30Row372
  , tttLargeFiber30Row373
  , tttLargeFiber30Row374
  , tttLargeFiber30Row375
  , tttLargeFiber30Row376
  , tttLargeFiber30Row377
  , tttLargeFiber30Row378
  , tttLargeFiber30Row379
  , tttLargeFiber30Row380
  , tttLargeFiber30Row381
  , tttLargeFiber30Row382
  , tttLargeFiber30Row383
  ]

def tttLargeFiber30Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber30Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber30Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber30Block5Chunk3Sources

theorem tttLargeFiber30Block5Chunk3SourcesCheck_ok :
    tttLargeFiber30Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber30Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block5Chunk3RowValid
    (listGetD tttLargeFiber30Block5Chunk3Rows i default)

def tttLargeFiber30Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block5Chunk3Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block5Chunk3Sources 0 0 == 1744
      && tttLargeFiber30ParentOf 1744 == 112
      && tttLargeFiber30ParentOf 112 == 48
      && tttLargeFiber30ParentOf 48 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block5Chunk3Sources 1 0 == 1745
      && tttLargeFiber30ParentOf 1745 == 113
      && tttLargeFiber30ParentOf 113 == 49
      && tttLargeFiber30ParentOf 49 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block5Chunk3Sources 2 0 == 1746
      && tttLargeFiber30ParentOf 1746 == 114
      && tttLargeFiber30ParentOf 114 == 50
      && tttLargeFiber30ParentOf 50 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block5Chunk3Sources 3 0 == 1747
      && tttLargeFiber30ParentOf 1747 == 1731
      && tttLargeFiber30ParentOf 1731 == 1699
      && tttLargeFiber30ParentOf 1699 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block5Chunk3Sources 4 0 == 1748
      && tttLargeFiber30ParentOf 1748 == 1716
      && tttLargeFiber30ParentOf 1716 == 1704
      && tttLargeFiber30ParentOf 1704 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block5Chunk3Sources 5 0 == 1749
      && tttLargeFiber30ParentOf 1749 == 1717
      && tttLargeFiber30ParentOf 1717 == 1705
      && tttLargeFiber30ParentOf 1705 == 73
      && tttLargeFiber30ParentOf 73 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block5Chunk3Sources 6 0 == 1750
      && tttLargeFiber30ParentOf 1750 == 118
      && tttLargeFiber30ParentOf 118 == 54
      && tttLargeFiber30ParentOf 54 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block5Chunk3Sources 7 0 == 1751
      && tttLargeFiber30ParentOf 1751 == 119
      && tttLargeFiber30ParentOf 119 == 55
      && tttLargeFiber30ParentOf 55 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block5Chunk3Sources 8 0 == 1752
      && tttLargeFiber30ParentOf 1752 == 120
      && tttLargeFiber30ParentOf 120 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block5Chunk3Sources 9 0 == 1753
      && tttLargeFiber30ParentOf 1753 == 121
      && tttLargeFiber30ParentOf 121 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block5Chunk3Sources 10 0 == 1754
      && tttLargeFiber30ParentOf 1754 == 122
      && tttLargeFiber30ParentOf 122 == 58
      && tttLargeFiber30ParentOf 58 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block5Chunk3Sources 11 0 == 1755
      && tttLargeFiber30ParentOf 1755 == 123
      && tttLargeFiber30ParentOf 123 == 59
      && tttLargeFiber30ParentOf 59 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block5Chunk3Sources 12 0 == 1756
      && tttLargeFiber30ParentOf 1756 == 1724
      && tttLargeFiber30ParentOf 1724 == 1696
      && tttLargeFiber30ParentOf 1696 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block5Chunk3Sources 13 0 == 1757
      && tttLargeFiber30ParentOf 1757 == 1725
      && tttLargeFiber30ParentOf 1725 == 1697
      && tttLargeFiber30ParentOf 1697 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block5Chunk3Sources 14 0 == 1758
      && tttLargeFiber30ParentOf 1758 == 126
      && tttLargeFiber30ParentOf 126 == 62
      && tttLargeFiber30ParentOf 62 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block5Chunk3Sources 15 0 == 1759
      && tttLargeFiber30ParentOf 1759 == 127
      && tttLargeFiber30ParentOf 127 == 63
      && tttLargeFiber30ParentOf 63 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block5Chunk3Row_0_ok :
    tttLargeFiber30Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_1_ok :
    tttLargeFiber30Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_2_ok :
    tttLargeFiber30Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_3_ok :
    tttLargeFiber30Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_4_ok :
    tttLargeFiber30Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_5_ok :
    tttLargeFiber30Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_6_ok :
    tttLargeFiber30Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_7_ok :
    tttLargeFiber30Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_8_ok :
    tttLargeFiber30Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_9_ok :
    tttLargeFiber30Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_10_ok :
    tttLargeFiber30Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_11_ok :
    tttLargeFiber30Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_12_ok :
    tttLargeFiber30Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_13_ok :
    tttLargeFiber30Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_14_ok :
    tttLargeFiber30Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3Row_15_ok :
    tttLargeFiber30Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_0_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_1_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_2_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_3_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_4_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_5_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_6_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_7_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_8_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_9_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_10_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_11_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_12_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_13_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_14_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentMap_15_ok :
    tttLargeFiber30Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_0_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_1_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_2_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_3_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_4_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_5_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_6_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_7_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_8_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_9_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_10_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_11_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_12_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_13_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_14_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block5Chunk3ParentPath_15_ok :
    tttLargeFiber30Block5Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber30Block5Chunk3RowCheck 0
    && tttLargeFiber30Block5Chunk3RowCheck 1
    && tttLargeFiber30Block5Chunk3RowCheck 2
    && tttLargeFiber30Block5Chunk3RowCheck 3
    && tttLargeFiber30Block5Chunk3RowCheck 4
    && tttLargeFiber30Block5Chunk3RowCheck 5
    && tttLargeFiber30Block5Chunk3RowCheck 6
    && tttLargeFiber30Block5Chunk3RowCheck 7
    && tttLargeFiber30Block5Chunk3RowCheck 8
    && tttLargeFiber30Block5Chunk3RowCheck 9
    && tttLargeFiber30Block5Chunk3RowCheck 10
    && tttLargeFiber30Block5Chunk3RowCheck 11
    && tttLargeFiber30Block5Chunk3RowCheck 12
    && tttLargeFiber30Block5Chunk3RowCheck 13
    && tttLargeFiber30Block5Chunk3RowCheck 14
    && tttLargeFiber30Block5Chunk3RowCheck 15

theorem tttLargeFiber30Block5Chunk3RowsAudit_ok :
    tttLargeFiber30Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber30Block5Chunk3RowsAudit,
    tttLargeFiber30Block5Chunk3Row_0_ok,
    tttLargeFiber30Block5Chunk3Row_1_ok,
    tttLargeFiber30Block5Chunk3Row_2_ok,
    tttLargeFiber30Block5Chunk3Row_3_ok,
    tttLargeFiber30Block5Chunk3Row_4_ok,
    tttLargeFiber30Block5Chunk3Row_5_ok,
    tttLargeFiber30Block5Chunk3Row_6_ok,
    tttLargeFiber30Block5Chunk3Row_7_ok,
    tttLargeFiber30Block5Chunk3Row_8_ok,
    tttLargeFiber30Block5Chunk3Row_9_ok,
    tttLargeFiber30Block5Chunk3Row_10_ok,
    tttLargeFiber30Block5Chunk3Row_11_ok,
    tttLargeFiber30Block5Chunk3Row_12_ok,
    tttLargeFiber30Block5Chunk3Row_13_ok,
    tttLargeFiber30Block5Chunk3Row_14_ok,
    tttLargeFiber30Block5Chunk3Row_15_ok]

def tttLargeFiber30Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber30Block5Chunk3ParentMapCheck 0
    && tttLargeFiber30Block5Chunk3ParentMapCheck 1
    && tttLargeFiber30Block5Chunk3ParentMapCheck 2
    && tttLargeFiber30Block5Chunk3ParentMapCheck 3
    && tttLargeFiber30Block5Chunk3ParentMapCheck 4
    && tttLargeFiber30Block5Chunk3ParentMapCheck 5
    && tttLargeFiber30Block5Chunk3ParentMapCheck 6
    && tttLargeFiber30Block5Chunk3ParentMapCheck 7
    && tttLargeFiber30Block5Chunk3ParentMapCheck 8
    && tttLargeFiber30Block5Chunk3ParentMapCheck 9
    && tttLargeFiber30Block5Chunk3ParentMapCheck 10
    && tttLargeFiber30Block5Chunk3ParentMapCheck 11
    && tttLargeFiber30Block5Chunk3ParentMapCheck 12
    && tttLargeFiber30Block5Chunk3ParentMapCheck 13
    && tttLargeFiber30Block5Chunk3ParentMapCheck 14
    && tttLargeFiber30Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber30Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber30Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber30Block5Chunk3ParentMapAudit,
    tttLargeFiber30Block5Chunk3ParentMap_0_ok,
    tttLargeFiber30Block5Chunk3ParentMap_1_ok,
    tttLargeFiber30Block5Chunk3ParentMap_2_ok,
    tttLargeFiber30Block5Chunk3ParentMap_3_ok,
    tttLargeFiber30Block5Chunk3ParentMap_4_ok,
    tttLargeFiber30Block5Chunk3ParentMap_5_ok,
    tttLargeFiber30Block5Chunk3ParentMap_6_ok,
    tttLargeFiber30Block5Chunk3ParentMap_7_ok,
    tttLargeFiber30Block5Chunk3ParentMap_8_ok,
    tttLargeFiber30Block5Chunk3ParentMap_9_ok,
    tttLargeFiber30Block5Chunk3ParentMap_10_ok,
    tttLargeFiber30Block5Chunk3ParentMap_11_ok,
    tttLargeFiber30Block5Chunk3ParentMap_12_ok,
    tttLargeFiber30Block5Chunk3ParentMap_13_ok,
    tttLargeFiber30Block5Chunk3ParentMap_14_ok,
    tttLargeFiber30Block5Chunk3ParentMap_15_ok]

def tttLargeFiber30Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber30Block5Chunk3ParentPathCheck 0
    && tttLargeFiber30Block5Chunk3ParentPathCheck 1
    && tttLargeFiber30Block5Chunk3ParentPathCheck 2
    && tttLargeFiber30Block5Chunk3ParentPathCheck 3
    && tttLargeFiber30Block5Chunk3ParentPathCheck 4
    && tttLargeFiber30Block5Chunk3ParentPathCheck 5
    && tttLargeFiber30Block5Chunk3ParentPathCheck 6
    && tttLargeFiber30Block5Chunk3ParentPathCheck 7
    && tttLargeFiber30Block5Chunk3ParentPathCheck 8
    && tttLargeFiber30Block5Chunk3ParentPathCheck 9
    && tttLargeFiber30Block5Chunk3ParentPathCheck 10
    && tttLargeFiber30Block5Chunk3ParentPathCheck 11
    && tttLargeFiber30Block5Chunk3ParentPathCheck 12
    && tttLargeFiber30Block5Chunk3ParentPathCheck 13
    && tttLargeFiber30Block5Chunk3ParentPathCheck 14
    && tttLargeFiber30Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber30Block5Chunk3ParentsAudit_ok :
    tttLargeFiber30Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber30Block5Chunk3ParentsAudit,
    tttLargeFiber30Block5Chunk3ParentPath_0_ok,
    tttLargeFiber30Block5Chunk3ParentPath_1_ok,
    tttLargeFiber30Block5Chunk3ParentPath_2_ok,
    tttLargeFiber30Block5Chunk3ParentPath_3_ok,
    tttLargeFiber30Block5Chunk3ParentPath_4_ok,
    tttLargeFiber30Block5Chunk3ParentPath_5_ok,
    tttLargeFiber30Block5Chunk3ParentPath_6_ok,
    tttLargeFiber30Block5Chunk3ParentPath_7_ok,
    tttLargeFiber30Block5Chunk3ParentPath_8_ok,
    tttLargeFiber30Block5Chunk3ParentPath_9_ok,
    tttLargeFiber30Block5Chunk3ParentPath_10_ok,
    tttLargeFiber30Block5Chunk3ParentPath_11_ok,
    tttLargeFiber30Block5Chunk3ParentPath_12_ok,
    tttLargeFiber30Block5Chunk3ParentPath_13_ok,
    tttLargeFiber30Block5Chunk3ParentPath_14_ok,
    tttLargeFiber30Block5Chunk3ParentPath_15_ok]

def tttLargeFiber30Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block5Chunk3SourcesCheck &&
    tttLargeFiber30Block5Chunk3RowsAudit &&
    tttLargeFiber30Block5Chunk3ParentMapAudit &&
    tttLargeFiber30Block5Chunk3ParentsAudit

theorem tttLargeFiber30Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber30Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block5Chunk3SourcesCheck_ok,
    tttLargeFiber30Block5Chunk3RowsAudit_ok,
    tttLargeFiber30Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber30Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
