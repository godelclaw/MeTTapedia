import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 5 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block5Chunk3Sources : List Nat :=
  [   1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479,
   1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]

def tttLargeFiber72Row368 : TripleComponentParentRow :=
  tripleRow 1472 928 41 174 64 25 110 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row369 : TripleComponentParentRow :=
  tripleRow 1473 929 41 174 65 25 110 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row370 : TripleComponentParentRow :=
  tripleRow 1474 930 41 174 66 25 110 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row371 : TripleComponentParentRow :=
  tripleRow 1475 1459 41 174 67 41 172 135
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

def tttLargeFiber72Row372 : TripleComponentParentRow :=
  tripleRow 1476 1444 41 174 116 41 158 48
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

def tttLargeFiber72Row373 : TripleComponentParentRow :=
  tripleRow 1477 1445 41 174 117 41 158 49
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

def tttLargeFiber72Row374 : TripleComponentParentRow :=
  tripleRow 1478 934 41 174 118 25 110 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row375 : TripleComponentParentRow :=
  tripleRow 1479 935 41 174 119 25 110 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row376 : TripleComponentParentRow :=
  tripleRow 1480 936 41 175 72 25 111 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row377 : TripleComponentParentRow :=
  tripleRow 1481 937 41 175 73 25 111 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row378 : TripleComponentParentRow :=
  tripleRow 1482 938 41 175 74 25 111 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row379 : TripleComponentParentRow :=
  tripleRow 1483 939 41 175 75 25 111 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row380 : TripleComponentParentRow :=
  tripleRow 1484 1452 41 175 124 41 159 56
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

def tttLargeFiber72Row381 : TripleComponentParentRow :=
  tripleRow 1485 1453 41 175 125 41 159 57
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

def tttLargeFiber72Row382 : TripleComponentParentRow :=
  tripleRow 1486 942 41 175 126 25 111 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row383 : TripleComponentParentRow :=
  tripleRow 1487 943 41 175 127 25 111 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row368
  , tttLargeFiber72Row369
  , tttLargeFiber72Row370
  , tttLargeFiber72Row371
  , tttLargeFiber72Row372
  , tttLargeFiber72Row373
  , tttLargeFiber72Row374
  , tttLargeFiber72Row375
  , tttLargeFiber72Row376
  , tttLargeFiber72Row377
  , tttLargeFiber72Row378
  , tttLargeFiber72Row379
  , tttLargeFiber72Row380
  , tttLargeFiber72Row381
  , tttLargeFiber72Row382
  , tttLargeFiber72Row383
  ]

def tttLargeFiber72Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber72Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber72Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber72Block5Chunk3Sources

theorem tttLargeFiber72Block5Chunk3SourcesCheck_ok :
    tttLargeFiber72Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber72Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block5Chunk3RowValid
    (listGetD tttLargeFiber72Block5Chunk3Rows i default)

def tttLargeFiber72Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block5Chunk3Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block5Chunk3Sources 0 0 == 1472
      && tttLargeFiber72ParentOf 1472 == 928
      && tttLargeFiber72ParentOf 928 == 864
      && tttLargeFiber72ParentOf 864 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block5Chunk3Sources 1 0 == 1473
      && tttLargeFiber72ParentOf 1473 == 929
      && tttLargeFiber72ParentOf 929 == 865
      && tttLargeFiber72ParentOf 865 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block5Chunk3Sources 2 0 == 1474
      && tttLargeFiber72ParentOf 1474 == 930
      && tttLargeFiber72ParentOf 930 == 866
      && tttLargeFiber72ParentOf 866 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block5Chunk3Sources 3 0 == 1475
      && tttLargeFiber72ParentOf 1475 == 1459
      && tttLargeFiber72ParentOf 1459 == 1427
      && tttLargeFiber72ParentOf 1427 == 1424
      && tttLargeFiber72ParentOf 1424 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block5Chunk3Sources 4 0 == 1476
      && tttLargeFiber72ParentOf 1476 == 1444
      && tttLargeFiber72ParentOf 1444 == 1432
      && tttLargeFiber72ParentOf 1432 == 888
      && tttLargeFiber72ParentOf 888 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block5Chunk3Sources 5 0 == 1477
      && tttLargeFiber72ParentOf 1477 == 1445
      && tttLargeFiber72ParentOf 1445 == 1433
      && tttLargeFiber72ParentOf 1433 == 889
      && tttLargeFiber72ParentOf 889 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (6 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block5Chunk3Sources 6 0 == 1478
      && tttLargeFiber72ParentOf 1478 == 934
      && tttLargeFiber72ParentOf 934 == 870
      && tttLargeFiber72ParentOf 870 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (6 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block5Chunk3Sources 7 0 == 1479
      && tttLargeFiber72ParentOf 1479 == 935
      && tttLargeFiber72ParentOf 935 == 871
      && tttLargeFiber72ParentOf 871 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block5Chunk3Sources 8 0 == 1480
      && tttLargeFiber72ParentOf 1480 == 936
      && tttLargeFiber72ParentOf 936 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block5Chunk3Sources 9 0 == 1481
      && tttLargeFiber72ParentOf 1481 == 937
      && tttLargeFiber72ParentOf 937 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block5Chunk3Sources 10 0 == 1482
      && tttLargeFiber72ParentOf 1482 == 938
      && tttLargeFiber72ParentOf 938 == 874
      && tttLargeFiber72ParentOf 874 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block5Chunk3Sources 11 0 == 1483
      && tttLargeFiber72ParentOf 1483 == 939
      && tttLargeFiber72ParentOf 939 == 875
      && tttLargeFiber72ParentOf 875 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block5Chunk3Sources 12 0 == 1484
      && tttLargeFiber72ParentOf 1484 == 1452
      && tttLargeFiber72ParentOf 1452 == 1424
      && tttLargeFiber72ParentOf 1424 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block5Chunk3Sources 13 0 == 1485
      && tttLargeFiber72ParentOf 1485 == 1453
      && tttLargeFiber72ParentOf 1453 == 1425
      && tttLargeFiber72ParentOf 1425 == 881
      && tttLargeFiber72ParentOf 881 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block5Chunk3Sources 14 0 == 1486
      && tttLargeFiber72ParentOf 1486 == 942
      && tttLargeFiber72ParentOf 942 == 878
      && tttLargeFiber72ParentOf 878 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block5Chunk3Sources 15 0 == 1487
      && tttLargeFiber72ParentOf 1487 == 943
      && tttLargeFiber72ParentOf 943 == 879
      && tttLargeFiber72ParentOf 879 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block5Chunk3Row_0_ok :
    tttLargeFiber72Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_1_ok :
    tttLargeFiber72Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_2_ok :
    tttLargeFiber72Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_3_ok :
    tttLargeFiber72Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_4_ok :
    tttLargeFiber72Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_5_ok :
    tttLargeFiber72Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_6_ok :
    tttLargeFiber72Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_7_ok :
    tttLargeFiber72Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_8_ok :
    tttLargeFiber72Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_9_ok :
    tttLargeFiber72Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_10_ok :
    tttLargeFiber72Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_11_ok :
    tttLargeFiber72Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_12_ok :
    tttLargeFiber72Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_13_ok :
    tttLargeFiber72Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_14_ok :
    tttLargeFiber72Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3Row_15_ok :
    tttLargeFiber72Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_0_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_1_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_2_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_3_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_4_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_5_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_6_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_7_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_8_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_9_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_10_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_11_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_12_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_13_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_14_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentMap_15_ok :
    tttLargeFiber72Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_0_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_1_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_2_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_3_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_4_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_5_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_6_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_7_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_8_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_9_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_10_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_11_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_12_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_13_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_14_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block5Chunk3ParentPath_15_ok :
    tttLargeFiber72Block5Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber72Block5Chunk3RowCheck 0
    && tttLargeFiber72Block5Chunk3RowCheck 1
    && tttLargeFiber72Block5Chunk3RowCheck 2
    && tttLargeFiber72Block5Chunk3RowCheck 3
    && tttLargeFiber72Block5Chunk3RowCheck 4
    && tttLargeFiber72Block5Chunk3RowCheck 5
    && tttLargeFiber72Block5Chunk3RowCheck 6
    && tttLargeFiber72Block5Chunk3RowCheck 7
    && tttLargeFiber72Block5Chunk3RowCheck 8
    && tttLargeFiber72Block5Chunk3RowCheck 9
    && tttLargeFiber72Block5Chunk3RowCheck 10
    && tttLargeFiber72Block5Chunk3RowCheck 11
    && tttLargeFiber72Block5Chunk3RowCheck 12
    && tttLargeFiber72Block5Chunk3RowCheck 13
    && tttLargeFiber72Block5Chunk3RowCheck 14
    && tttLargeFiber72Block5Chunk3RowCheck 15

theorem tttLargeFiber72Block5Chunk3RowsAudit_ok :
    tttLargeFiber72Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber72Block5Chunk3RowsAudit,
    tttLargeFiber72Block5Chunk3Row_0_ok,
    tttLargeFiber72Block5Chunk3Row_1_ok,
    tttLargeFiber72Block5Chunk3Row_2_ok,
    tttLargeFiber72Block5Chunk3Row_3_ok,
    tttLargeFiber72Block5Chunk3Row_4_ok,
    tttLargeFiber72Block5Chunk3Row_5_ok,
    tttLargeFiber72Block5Chunk3Row_6_ok,
    tttLargeFiber72Block5Chunk3Row_7_ok,
    tttLargeFiber72Block5Chunk3Row_8_ok,
    tttLargeFiber72Block5Chunk3Row_9_ok,
    tttLargeFiber72Block5Chunk3Row_10_ok,
    tttLargeFiber72Block5Chunk3Row_11_ok,
    tttLargeFiber72Block5Chunk3Row_12_ok,
    tttLargeFiber72Block5Chunk3Row_13_ok,
    tttLargeFiber72Block5Chunk3Row_14_ok,
    tttLargeFiber72Block5Chunk3Row_15_ok]

def tttLargeFiber72Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber72Block5Chunk3ParentMapCheck 0
    && tttLargeFiber72Block5Chunk3ParentMapCheck 1
    && tttLargeFiber72Block5Chunk3ParentMapCheck 2
    && tttLargeFiber72Block5Chunk3ParentMapCheck 3
    && tttLargeFiber72Block5Chunk3ParentMapCheck 4
    && tttLargeFiber72Block5Chunk3ParentMapCheck 5
    && tttLargeFiber72Block5Chunk3ParentMapCheck 6
    && tttLargeFiber72Block5Chunk3ParentMapCheck 7
    && tttLargeFiber72Block5Chunk3ParentMapCheck 8
    && tttLargeFiber72Block5Chunk3ParentMapCheck 9
    && tttLargeFiber72Block5Chunk3ParentMapCheck 10
    && tttLargeFiber72Block5Chunk3ParentMapCheck 11
    && tttLargeFiber72Block5Chunk3ParentMapCheck 12
    && tttLargeFiber72Block5Chunk3ParentMapCheck 13
    && tttLargeFiber72Block5Chunk3ParentMapCheck 14
    && tttLargeFiber72Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber72Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber72Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber72Block5Chunk3ParentMapAudit,
    tttLargeFiber72Block5Chunk3ParentMap_0_ok,
    tttLargeFiber72Block5Chunk3ParentMap_1_ok,
    tttLargeFiber72Block5Chunk3ParentMap_2_ok,
    tttLargeFiber72Block5Chunk3ParentMap_3_ok,
    tttLargeFiber72Block5Chunk3ParentMap_4_ok,
    tttLargeFiber72Block5Chunk3ParentMap_5_ok,
    tttLargeFiber72Block5Chunk3ParentMap_6_ok,
    tttLargeFiber72Block5Chunk3ParentMap_7_ok,
    tttLargeFiber72Block5Chunk3ParentMap_8_ok,
    tttLargeFiber72Block5Chunk3ParentMap_9_ok,
    tttLargeFiber72Block5Chunk3ParentMap_10_ok,
    tttLargeFiber72Block5Chunk3ParentMap_11_ok,
    tttLargeFiber72Block5Chunk3ParentMap_12_ok,
    tttLargeFiber72Block5Chunk3ParentMap_13_ok,
    tttLargeFiber72Block5Chunk3ParentMap_14_ok,
    tttLargeFiber72Block5Chunk3ParentMap_15_ok]

def tttLargeFiber72Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber72Block5Chunk3ParentPathCheck 0
    && tttLargeFiber72Block5Chunk3ParentPathCheck 1
    && tttLargeFiber72Block5Chunk3ParentPathCheck 2
    && tttLargeFiber72Block5Chunk3ParentPathCheck 3
    && tttLargeFiber72Block5Chunk3ParentPathCheck 4
    && tttLargeFiber72Block5Chunk3ParentPathCheck 5
    && tttLargeFiber72Block5Chunk3ParentPathCheck 6
    && tttLargeFiber72Block5Chunk3ParentPathCheck 7
    && tttLargeFiber72Block5Chunk3ParentPathCheck 8
    && tttLargeFiber72Block5Chunk3ParentPathCheck 9
    && tttLargeFiber72Block5Chunk3ParentPathCheck 10
    && tttLargeFiber72Block5Chunk3ParentPathCheck 11
    && tttLargeFiber72Block5Chunk3ParentPathCheck 12
    && tttLargeFiber72Block5Chunk3ParentPathCheck 13
    && tttLargeFiber72Block5Chunk3ParentPathCheck 14
    && tttLargeFiber72Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber72Block5Chunk3ParentsAudit_ok :
    tttLargeFiber72Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber72Block5Chunk3ParentsAudit,
    tttLargeFiber72Block5Chunk3ParentPath_0_ok,
    tttLargeFiber72Block5Chunk3ParentPath_1_ok,
    tttLargeFiber72Block5Chunk3ParentPath_2_ok,
    tttLargeFiber72Block5Chunk3ParentPath_3_ok,
    tttLargeFiber72Block5Chunk3ParentPath_4_ok,
    tttLargeFiber72Block5Chunk3ParentPath_5_ok,
    tttLargeFiber72Block5Chunk3ParentPath_6_ok,
    tttLargeFiber72Block5Chunk3ParentPath_7_ok,
    tttLargeFiber72Block5Chunk3ParentPath_8_ok,
    tttLargeFiber72Block5Chunk3ParentPath_9_ok,
    tttLargeFiber72Block5Chunk3ParentPath_10_ok,
    tttLargeFiber72Block5Chunk3ParentPath_11_ok,
    tttLargeFiber72Block5Chunk3ParentPath_12_ok,
    tttLargeFiber72Block5Chunk3ParentPath_13_ok,
    tttLargeFiber72Block5Chunk3ParentPath_14_ok,
    tttLargeFiber72Block5Chunk3ParentPath_15_ok]

def tttLargeFiber72Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block5Chunk3SourcesCheck &&
    tttLargeFiber72Block5Chunk3RowsAudit &&
    tttLargeFiber72Block5Chunk3ParentMapAudit &&
    tttLargeFiber72Block5Chunk3ParentsAudit

theorem tttLargeFiber72Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber72Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block5Chunk3SourcesCheck_ok,
    tttLargeFiber72Block5Chunk3RowsAudit_ok,
    tttLargeFiber72Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber72Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
