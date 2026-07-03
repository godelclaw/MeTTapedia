import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 5 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block5Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block5Chunk0Sources : List Nat :=
  [   1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431,
   1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]

def tttLargeFiber72Row320 : TripleComponentParentRow :=
  tripleRow 1424 880 41 156 148 25 88 80
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

def tttLargeFiber72Row321 : TripleComponentParentRow :=
  tripleRow 1425 881 41 156 149 25 88 81
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

def tttLargeFiber72Row322 : TripleComponentParentRow :=
  tripleRow 1426 882 41 156 150 25 88 82
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

def tttLargeFiber72Row323 : TripleComponentParentRow :=
  tripleRow 1427 1424 41 156 151 41 156 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row324 : TripleComponentParentRow :=
  tripleRow 1428 1424 41 156 164 41 156 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row325 : TripleComponentParentRow :=
  tripleRow 1429 1425 41 156 165 41 156 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row326 : TripleComponentParentRow :=
  tripleRow 1430 886 41 156 166 25 88 102
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

def tttLargeFiber72Row327 : TripleComponentParentRow :=
  tripleRow 1431 887 41 156 167 25 88 103
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

def tttLargeFiber72Row328 : TripleComponentParentRow :=
  tripleRow 1432 888 41 157 156 25 89 88
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

def tttLargeFiber72Row329 : TripleComponentParentRow :=
  tripleRow 1433 889 41 157 157 25 89 89
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

def tttLargeFiber72Row330 : TripleComponentParentRow :=
  tripleRow 1434 890 41 157 158 25 89 90
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

def tttLargeFiber72Row331 : TripleComponentParentRow :=
  tripleRow 1435 1432 41 157 159 41 157 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row332 : TripleComponentParentRow :=
  tripleRow 1436 1432 41 157 172 41 157 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row333 : TripleComponentParentRow :=
  tripleRow 1437 1433 41 157 173 41 157 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row334 : TripleComponentParentRow :=
  tripleRow 1438 894 41 157 174 25 89 110
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

def tttLargeFiber72Row335 : TripleComponentParentRow :=
  tripleRow 1439 895 41 157 175 25 89 111
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

def tttLargeFiber72Block5Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row320
  , tttLargeFiber72Row321
  , tttLargeFiber72Row322
  , tttLargeFiber72Row323
  , tttLargeFiber72Row324
  , tttLargeFiber72Row325
  , tttLargeFiber72Row326
  , tttLargeFiber72Row327
  , tttLargeFiber72Row328
  , tttLargeFiber72Row329
  , tttLargeFiber72Row330
  , tttLargeFiber72Row331
  , tttLargeFiber72Row332
  , tttLargeFiber72Row333
  , tttLargeFiber72Row334
  , tttLargeFiber72Row335
  ]

def tttLargeFiber72Block5Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block5Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block5Chunk0ExpectedContains row.source &&
    tttLargeFiber72Block5Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block5Chunk0SourcesCheck : Bool :=
  (tttLargeFiber72Block5Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber72Block5Chunk0Sources

theorem tttLargeFiber72Block5Chunk0SourcesCheck_ok :
    tttLargeFiber72Block5Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber72Block5Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block5Chunk0RowValid
    (listGetD tttLargeFiber72Block5Chunk0Rows i default)

def tttLargeFiber72Block5Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block5Chunk0Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block5Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block5Chunk0Sources 0 0 == 1424
      && tttLargeFiber72ParentOf 1424 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block5Chunk0Sources 1 0 == 1425
      && tttLargeFiber72ParentOf 1425 == 881
      && tttLargeFiber72ParentOf 881 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block5Chunk0Sources 2 0 == 1426
      && tttLargeFiber72ParentOf 1426 == 882
      && tttLargeFiber72ParentOf 882 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block5Chunk0Sources 3 0 == 1427
      && tttLargeFiber72ParentOf 1427 == 1424
      && tttLargeFiber72ParentOf 1424 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block5Chunk0Sources 4 0 == 1428
      && tttLargeFiber72ParentOf 1428 == 1424
      && tttLargeFiber72ParentOf 1424 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block5Chunk0Sources 5 0 == 1429
      && tttLargeFiber72ParentOf 1429 == 1425
      && tttLargeFiber72ParentOf 1425 == 881
      && tttLargeFiber72ParentOf 881 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block5Chunk0Sources 6 0 == 1430
      && tttLargeFiber72ParentOf 1430 == 886
      && tttLargeFiber72ParentOf 886 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block5Chunk0Sources 7 0 == 1431
      && tttLargeFiber72ParentOf 1431 == 887
      && tttLargeFiber72ParentOf 887 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block5Chunk0Sources 8 0 == 1432
      && tttLargeFiber72ParentOf 1432 == 888
      && tttLargeFiber72ParentOf 888 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block5Chunk0Sources 9 0 == 1433
      && tttLargeFiber72ParentOf 1433 == 889
      && tttLargeFiber72ParentOf 889 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block5Chunk0Sources 10 0 == 1434
      && tttLargeFiber72ParentOf 1434 == 890
      && tttLargeFiber72ParentOf 890 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block5Chunk0Sources 11 0 == 1435
      && tttLargeFiber72ParentOf 1435 == 1432
      && tttLargeFiber72ParentOf 1432 == 888
      && tttLargeFiber72ParentOf 888 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block5Chunk0Sources 12 0 == 1436
      && tttLargeFiber72ParentOf 1436 == 1432
      && tttLargeFiber72ParentOf 1432 == 888
      && tttLargeFiber72ParentOf 888 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block5Chunk0Sources 13 0 == 1437
      && tttLargeFiber72ParentOf 1437 == 1433
      && tttLargeFiber72ParentOf 1433 == 889
      && tttLargeFiber72ParentOf 889 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block5Chunk0Sources 14 0 == 1438
      && tttLargeFiber72ParentOf 1438 == 894
      && tttLargeFiber72ParentOf 894 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block5Chunk0Sources 15 0 == 1439
      && tttLargeFiber72ParentOf 1439 == 895
      && tttLargeFiber72ParentOf 895 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block5Chunk0Row_0_ok :
    tttLargeFiber72Block5Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_1_ok :
    tttLargeFiber72Block5Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_2_ok :
    tttLargeFiber72Block5Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_3_ok :
    tttLargeFiber72Block5Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_4_ok :
    tttLargeFiber72Block5Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_5_ok :
    tttLargeFiber72Block5Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_6_ok :
    tttLargeFiber72Block5Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_7_ok :
    tttLargeFiber72Block5Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_8_ok :
    tttLargeFiber72Block5Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_9_ok :
    tttLargeFiber72Block5Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_10_ok :
    tttLargeFiber72Block5Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_11_ok :
    tttLargeFiber72Block5Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_12_ok :
    tttLargeFiber72Block5Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_13_ok :
    tttLargeFiber72Block5Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_14_ok :
    tttLargeFiber72Block5Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0Row_15_ok :
    tttLargeFiber72Block5Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_0_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_1_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_2_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_3_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_4_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_5_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_6_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_7_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_8_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_9_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_10_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_11_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_12_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_13_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_14_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentMap_15_ok :
    tttLargeFiber72Block5Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_0_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_1_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_2_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_3_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_4_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_5_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_6_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_7_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_8_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_9_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_10_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_11_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_12_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_13_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_14_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block5Chunk0ParentPath_15_ok :
    tttLargeFiber72Block5Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block5Chunk0RowsAudit : Bool :=
  tttLargeFiber72Block5Chunk0RowCheck 0
    && tttLargeFiber72Block5Chunk0RowCheck 1
    && tttLargeFiber72Block5Chunk0RowCheck 2
    && tttLargeFiber72Block5Chunk0RowCheck 3
    && tttLargeFiber72Block5Chunk0RowCheck 4
    && tttLargeFiber72Block5Chunk0RowCheck 5
    && tttLargeFiber72Block5Chunk0RowCheck 6
    && tttLargeFiber72Block5Chunk0RowCheck 7
    && tttLargeFiber72Block5Chunk0RowCheck 8
    && tttLargeFiber72Block5Chunk0RowCheck 9
    && tttLargeFiber72Block5Chunk0RowCheck 10
    && tttLargeFiber72Block5Chunk0RowCheck 11
    && tttLargeFiber72Block5Chunk0RowCheck 12
    && tttLargeFiber72Block5Chunk0RowCheck 13
    && tttLargeFiber72Block5Chunk0RowCheck 14
    && tttLargeFiber72Block5Chunk0RowCheck 15

theorem tttLargeFiber72Block5Chunk0RowsAudit_ok :
    tttLargeFiber72Block5Chunk0RowsAudit = true := by
  simp [tttLargeFiber72Block5Chunk0RowsAudit,
    tttLargeFiber72Block5Chunk0Row_0_ok,
    tttLargeFiber72Block5Chunk0Row_1_ok,
    tttLargeFiber72Block5Chunk0Row_2_ok,
    tttLargeFiber72Block5Chunk0Row_3_ok,
    tttLargeFiber72Block5Chunk0Row_4_ok,
    tttLargeFiber72Block5Chunk0Row_5_ok,
    tttLargeFiber72Block5Chunk0Row_6_ok,
    tttLargeFiber72Block5Chunk0Row_7_ok,
    tttLargeFiber72Block5Chunk0Row_8_ok,
    tttLargeFiber72Block5Chunk0Row_9_ok,
    tttLargeFiber72Block5Chunk0Row_10_ok,
    tttLargeFiber72Block5Chunk0Row_11_ok,
    tttLargeFiber72Block5Chunk0Row_12_ok,
    tttLargeFiber72Block5Chunk0Row_13_ok,
    tttLargeFiber72Block5Chunk0Row_14_ok,
    tttLargeFiber72Block5Chunk0Row_15_ok]

def tttLargeFiber72Block5Chunk0ParentMapAudit : Bool :=
  tttLargeFiber72Block5Chunk0ParentMapCheck 0
    && tttLargeFiber72Block5Chunk0ParentMapCheck 1
    && tttLargeFiber72Block5Chunk0ParentMapCheck 2
    && tttLargeFiber72Block5Chunk0ParentMapCheck 3
    && tttLargeFiber72Block5Chunk0ParentMapCheck 4
    && tttLargeFiber72Block5Chunk0ParentMapCheck 5
    && tttLargeFiber72Block5Chunk0ParentMapCheck 6
    && tttLargeFiber72Block5Chunk0ParentMapCheck 7
    && tttLargeFiber72Block5Chunk0ParentMapCheck 8
    && tttLargeFiber72Block5Chunk0ParentMapCheck 9
    && tttLargeFiber72Block5Chunk0ParentMapCheck 10
    && tttLargeFiber72Block5Chunk0ParentMapCheck 11
    && tttLargeFiber72Block5Chunk0ParentMapCheck 12
    && tttLargeFiber72Block5Chunk0ParentMapCheck 13
    && tttLargeFiber72Block5Chunk0ParentMapCheck 14
    && tttLargeFiber72Block5Chunk0ParentMapCheck 15

theorem tttLargeFiber72Block5Chunk0ParentMapAudit_ok :
    tttLargeFiber72Block5Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber72Block5Chunk0ParentMapAudit,
    tttLargeFiber72Block5Chunk0ParentMap_0_ok,
    tttLargeFiber72Block5Chunk0ParentMap_1_ok,
    tttLargeFiber72Block5Chunk0ParentMap_2_ok,
    tttLargeFiber72Block5Chunk0ParentMap_3_ok,
    tttLargeFiber72Block5Chunk0ParentMap_4_ok,
    tttLargeFiber72Block5Chunk0ParentMap_5_ok,
    tttLargeFiber72Block5Chunk0ParentMap_6_ok,
    tttLargeFiber72Block5Chunk0ParentMap_7_ok,
    tttLargeFiber72Block5Chunk0ParentMap_8_ok,
    tttLargeFiber72Block5Chunk0ParentMap_9_ok,
    tttLargeFiber72Block5Chunk0ParentMap_10_ok,
    tttLargeFiber72Block5Chunk0ParentMap_11_ok,
    tttLargeFiber72Block5Chunk0ParentMap_12_ok,
    tttLargeFiber72Block5Chunk0ParentMap_13_ok,
    tttLargeFiber72Block5Chunk0ParentMap_14_ok,
    tttLargeFiber72Block5Chunk0ParentMap_15_ok]

def tttLargeFiber72Block5Chunk0ParentsAudit : Bool :=
  tttLargeFiber72Block5Chunk0ParentPathCheck 0
    && tttLargeFiber72Block5Chunk0ParentPathCheck 1
    && tttLargeFiber72Block5Chunk0ParentPathCheck 2
    && tttLargeFiber72Block5Chunk0ParentPathCheck 3
    && tttLargeFiber72Block5Chunk0ParentPathCheck 4
    && tttLargeFiber72Block5Chunk0ParentPathCheck 5
    && tttLargeFiber72Block5Chunk0ParentPathCheck 6
    && tttLargeFiber72Block5Chunk0ParentPathCheck 7
    && tttLargeFiber72Block5Chunk0ParentPathCheck 8
    && tttLargeFiber72Block5Chunk0ParentPathCheck 9
    && tttLargeFiber72Block5Chunk0ParentPathCheck 10
    && tttLargeFiber72Block5Chunk0ParentPathCheck 11
    && tttLargeFiber72Block5Chunk0ParentPathCheck 12
    && tttLargeFiber72Block5Chunk0ParentPathCheck 13
    && tttLargeFiber72Block5Chunk0ParentPathCheck 14
    && tttLargeFiber72Block5Chunk0ParentPathCheck 15

theorem tttLargeFiber72Block5Chunk0ParentsAudit_ok :
    tttLargeFiber72Block5Chunk0ParentsAudit = true := by
  simp [tttLargeFiber72Block5Chunk0ParentsAudit,
    tttLargeFiber72Block5Chunk0ParentPath_0_ok,
    tttLargeFiber72Block5Chunk0ParentPath_1_ok,
    tttLargeFiber72Block5Chunk0ParentPath_2_ok,
    tttLargeFiber72Block5Chunk0ParentPath_3_ok,
    tttLargeFiber72Block5Chunk0ParentPath_4_ok,
    tttLargeFiber72Block5Chunk0ParentPath_5_ok,
    tttLargeFiber72Block5Chunk0ParentPath_6_ok,
    tttLargeFiber72Block5Chunk0ParentPath_7_ok,
    tttLargeFiber72Block5Chunk0ParentPath_8_ok,
    tttLargeFiber72Block5Chunk0ParentPath_9_ok,
    tttLargeFiber72Block5Chunk0ParentPath_10_ok,
    tttLargeFiber72Block5Chunk0ParentPath_11_ok,
    tttLargeFiber72Block5Chunk0ParentPath_12_ok,
    tttLargeFiber72Block5Chunk0ParentPath_13_ok,
    tttLargeFiber72Block5Chunk0ParentPath_14_ok,
    tttLargeFiber72Block5Chunk0ParentPath_15_ok]

def tttLargeFiber72Block5Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block5Chunk0SourcesCheck &&
    tttLargeFiber72Block5Chunk0RowsAudit &&
    tttLargeFiber72Block5Chunk0ParentMapAudit &&
    tttLargeFiber72Block5Chunk0ParentsAudit

theorem tttLargeFiber72Block5Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber72Block5Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block5Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block5Chunk0SourcesCheck_ok,
    tttLargeFiber72Block5Chunk0RowsAudit_ok,
    tttLargeFiber72Block5Chunk0ParentMapAudit_ok,
    tttLargeFiber72Block5Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block5Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
