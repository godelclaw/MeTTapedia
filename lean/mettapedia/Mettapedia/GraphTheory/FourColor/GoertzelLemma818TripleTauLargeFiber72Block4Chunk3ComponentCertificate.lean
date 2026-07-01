import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 4 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block4Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block4Chunk3Sources : List Nat :=
  [   1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415,
   1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]

def tttLargeFiber72Row304 : TripleComponentParentRow :=
  tripleRow 1408 864 40 166 64 24 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row305 : TripleComponentParentRow :=
  tripleRow 1409 865 40 166 65 24 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row306 : TripleComponentParentRow :=
  tripleRow 1410 866 40 166 66 24 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row307 : TripleComponentParentRow :=
  tripleRow 1411 1395 40 166 67 40 164 135
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

def tttLargeFiber72Row308 : TripleComponentParentRow :=
  tripleRow 1412 1380 40 166 116 40 150 48
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

def tttLargeFiber72Row309 : TripleComponentParentRow :=
  tripleRow 1413 1381 40 166 117 40 150 49
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

def tttLargeFiber72Row310 : TripleComponentParentRow :=
  tripleRow 1414 870 40 166 118 24 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row311 : TripleComponentParentRow :=
  tripleRow 1415 871 40 166 119 24 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row312 : TripleComponentParentRow :=
  tripleRow 1416 872 40 167 72 24 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row313 : TripleComponentParentRow :=
  tripleRow 1417 873 40 167 73 24 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row314 : TripleComponentParentRow :=
  tripleRow 1418 874 40 167 74 24 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row315 : TripleComponentParentRow :=
  tripleRow 1419 875 40 167 75 24 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row316 : TripleComponentParentRow :=
  tripleRow 1420 1388 40 167 124 40 151 56
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

def tttLargeFiber72Row317 : TripleComponentParentRow :=
  tripleRow 1421 1389 40 167 125 40 151 57
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

def tttLargeFiber72Row318 : TripleComponentParentRow :=
  tripleRow 1422 878 40 167 126 24 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Row319 : TripleComponentParentRow :=
  tripleRow 1423 879 40 167 127 24 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber72Block4Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row304
  , tttLargeFiber72Row305
  , tttLargeFiber72Row306
  , tttLargeFiber72Row307
  , tttLargeFiber72Row308
  , tttLargeFiber72Row309
  , tttLargeFiber72Row310
  , tttLargeFiber72Row311
  , tttLargeFiber72Row312
  , tttLargeFiber72Row313
  , tttLargeFiber72Row314
  , tttLargeFiber72Row315
  , tttLargeFiber72Row316
  , tttLargeFiber72Row317
  , tttLargeFiber72Row318
  , tttLargeFiber72Row319
  ]

def tttLargeFiber72Block4Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block4Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block4Chunk3ExpectedContains row.source &&
    tttLargeFiber72Block4Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block4Chunk3SourcesCheck : Bool :=
  (tttLargeFiber72Block4Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber72Block4Chunk3Sources

theorem tttLargeFiber72Block4Chunk3SourcesCheck_ok :
    tttLargeFiber72Block4Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber72Block4Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block4Chunk3RowValid
    (listGetD tttLargeFiber72Block4Chunk3Rows i default)

def tttLargeFiber72Block4Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block4Chunk3Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block4Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block4Chunk3Sources 0 0 == 1408
      && tttLargeFiber72ParentOf 1408 == 864
      && tttLargeFiber72ParentOf 864 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block4Chunk3Sources 1 0 == 1409
      && tttLargeFiber72ParentOf 1409 == 865
      && tttLargeFiber72ParentOf 865 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block4Chunk3Sources 2 0 == 1410
      && tttLargeFiber72ParentOf 1410 == 866
      && tttLargeFiber72ParentOf 866 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block4Chunk3Sources 3 0 == 1411
      && tttLargeFiber72ParentOf 1411 == 1395
      && tttLargeFiber72ParentOf 1395 == 1363
      && tttLargeFiber72ParentOf 1363 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block4Chunk3Sources 4 0 == 1412
      && tttLargeFiber72ParentOf 1412 == 1380
      && tttLargeFiber72ParentOf 1380 == 1368
      && tttLargeFiber72ParentOf 1368 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block4Chunk3Sources 5 0 == 1413
      && tttLargeFiber72ParentOf 1413 == 1381
      && tttLargeFiber72ParentOf 1381 == 1369
      && tttLargeFiber72ParentOf 1369 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block4Chunk3Sources 6 0 == 1414
      && tttLargeFiber72ParentOf 1414 == 870
      && tttLargeFiber72ParentOf 870 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block4Chunk3Sources 7 0 == 1415
      && tttLargeFiber72ParentOf 1415 == 871
      && tttLargeFiber72ParentOf 871 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block4Chunk3Sources 8 0 == 1416
      && tttLargeFiber72ParentOf 1416 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block4Chunk3Sources 9 0 == 1417
      && tttLargeFiber72ParentOf 1417 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block4Chunk3Sources 10 0 == 1418
      && tttLargeFiber72ParentOf 1418 == 874
      && tttLargeFiber72ParentOf 874 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block4Chunk3Sources 11 0 == 1419
      && tttLargeFiber72ParentOf 1419 == 875
      && tttLargeFiber72ParentOf 875 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block4Chunk3Sources 12 0 == 1420
      && tttLargeFiber72ParentOf 1420 == 1388
      && tttLargeFiber72ParentOf 1388 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block4Chunk3Sources 13 0 == 1421
      && tttLargeFiber72ParentOf 1421 == 1389
      && tttLargeFiber72ParentOf 1389 == 1361
      && tttLargeFiber72ParentOf 1361 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block4Chunk3Sources 14 0 == 1422
      && tttLargeFiber72ParentOf 1422 == 878
      && tttLargeFiber72ParentOf 878 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block4Chunk3Sources 15 0 == 1423
      && tttLargeFiber72ParentOf 1423 == 879
      && tttLargeFiber72ParentOf 879 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block4Chunk3Row_0_ok :
    tttLargeFiber72Block4Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_1_ok :
    tttLargeFiber72Block4Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_2_ok :
    tttLargeFiber72Block4Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_3_ok :
    tttLargeFiber72Block4Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_4_ok :
    tttLargeFiber72Block4Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_5_ok :
    tttLargeFiber72Block4Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_6_ok :
    tttLargeFiber72Block4Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_7_ok :
    tttLargeFiber72Block4Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_8_ok :
    tttLargeFiber72Block4Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_9_ok :
    tttLargeFiber72Block4Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_10_ok :
    tttLargeFiber72Block4Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_11_ok :
    tttLargeFiber72Block4Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_12_ok :
    tttLargeFiber72Block4Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_13_ok :
    tttLargeFiber72Block4Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_14_ok :
    tttLargeFiber72Block4Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3Row_15_ok :
    tttLargeFiber72Block4Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_0_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_1_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_2_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_3_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_4_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_5_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_6_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_7_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_8_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_9_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_10_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_11_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_12_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_13_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_14_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentMap_15_ok :
    tttLargeFiber72Block4Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_0_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_1_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_2_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_3_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_4_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_5_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_6_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_7_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_8_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_9_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_10_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_11_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_12_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_13_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_14_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk3ParentPath_15_ok :
    tttLargeFiber72Block4Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block4Chunk3RowsAudit : Bool :=
  tttLargeFiber72Block4Chunk3RowCheck 0
    && tttLargeFiber72Block4Chunk3RowCheck 1
    && tttLargeFiber72Block4Chunk3RowCheck 2
    && tttLargeFiber72Block4Chunk3RowCheck 3
    && tttLargeFiber72Block4Chunk3RowCheck 4
    && tttLargeFiber72Block4Chunk3RowCheck 5
    && tttLargeFiber72Block4Chunk3RowCheck 6
    && tttLargeFiber72Block4Chunk3RowCheck 7
    && tttLargeFiber72Block4Chunk3RowCheck 8
    && tttLargeFiber72Block4Chunk3RowCheck 9
    && tttLargeFiber72Block4Chunk3RowCheck 10
    && tttLargeFiber72Block4Chunk3RowCheck 11
    && tttLargeFiber72Block4Chunk3RowCheck 12
    && tttLargeFiber72Block4Chunk3RowCheck 13
    && tttLargeFiber72Block4Chunk3RowCheck 14
    && tttLargeFiber72Block4Chunk3RowCheck 15

theorem tttLargeFiber72Block4Chunk3RowsAudit_ok :
    tttLargeFiber72Block4Chunk3RowsAudit = true := by
  simp [tttLargeFiber72Block4Chunk3RowsAudit,
    tttLargeFiber72Block4Chunk3Row_0_ok,
    tttLargeFiber72Block4Chunk3Row_1_ok,
    tttLargeFiber72Block4Chunk3Row_2_ok,
    tttLargeFiber72Block4Chunk3Row_3_ok,
    tttLargeFiber72Block4Chunk3Row_4_ok,
    tttLargeFiber72Block4Chunk3Row_5_ok,
    tttLargeFiber72Block4Chunk3Row_6_ok,
    tttLargeFiber72Block4Chunk3Row_7_ok,
    tttLargeFiber72Block4Chunk3Row_8_ok,
    tttLargeFiber72Block4Chunk3Row_9_ok,
    tttLargeFiber72Block4Chunk3Row_10_ok,
    tttLargeFiber72Block4Chunk3Row_11_ok,
    tttLargeFiber72Block4Chunk3Row_12_ok,
    tttLargeFiber72Block4Chunk3Row_13_ok,
    tttLargeFiber72Block4Chunk3Row_14_ok,
    tttLargeFiber72Block4Chunk3Row_15_ok]

def tttLargeFiber72Block4Chunk3ParentMapAudit : Bool :=
  tttLargeFiber72Block4Chunk3ParentMapCheck 0
    && tttLargeFiber72Block4Chunk3ParentMapCheck 1
    && tttLargeFiber72Block4Chunk3ParentMapCheck 2
    && tttLargeFiber72Block4Chunk3ParentMapCheck 3
    && tttLargeFiber72Block4Chunk3ParentMapCheck 4
    && tttLargeFiber72Block4Chunk3ParentMapCheck 5
    && tttLargeFiber72Block4Chunk3ParentMapCheck 6
    && tttLargeFiber72Block4Chunk3ParentMapCheck 7
    && tttLargeFiber72Block4Chunk3ParentMapCheck 8
    && tttLargeFiber72Block4Chunk3ParentMapCheck 9
    && tttLargeFiber72Block4Chunk3ParentMapCheck 10
    && tttLargeFiber72Block4Chunk3ParentMapCheck 11
    && tttLargeFiber72Block4Chunk3ParentMapCheck 12
    && tttLargeFiber72Block4Chunk3ParentMapCheck 13
    && tttLargeFiber72Block4Chunk3ParentMapCheck 14
    && tttLargeFiber72Block4Chunk3ParentMapCheck 15

theorem tttLargeFiber72Block4Chunk3ParentMapAudit_ok :
    tttLargeFiber72Block4Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber72Block4Chunk3ParentMapAudit,
    tttLargeFiber72Block4Chunk3ParentMap_0_ok,
    tttLargeFiber72Block4Chunk3ParentMap_1_ok,
    tttLargeFiber72Block4Chunk3ParentMap_2_ok,
    tttLargeFiber72Block4Chunk3ParentMap_3_ok,
    tttLargeFiber72Block4Chunk3ParentMap_4_ok,
    tttLargeFiber72Block4Chunk3ParentMap_5_ok,
    tttLargeFiber72Block4Chunk3ParentMap_6_ok,
    tttLargeFiber72Block4Chunk3ParentMap_7_ok,
    tttLargeFiber72Block4Chunk3ParentMap_8_ok,
    tttLargeFiber72Block4Chunk3ParentMap_9_ok,
    tttLargeFiber72Block4Chunk3ParentMap_10_ok,
    tttLargeFiber72Block4Chunk3ParentMap_11_ok,
    tttLargeFiber72Block4Chunk3ParentMap_12_ok,
    tttLargeFiber72Block4Chunk3ParentMap_13_ok,
    tttLargeFiber72Block4Chunk3ParentMap_14_ok,
    tttLargeFiber72Block4Chunk3ParentMap_15_ok]

def tttLargeFiber72Block4Chunk3ParentsAudit : Bool :=
  tttLargeFiber72Block4Chunk3ParentPathCheck 0
    && tttLargeFiber72Block4Chunk3ParentPathCheck 1
    && tttLargeFiber72Block4Chunk3ParentPathCheck 2
    && tttLargeFiber72Block4Chunk3ParentPathCheck 3
    && tttLargeFiber72Block4Chunk3ParentPathCheck 4
    && tttLargeFiber72Block4Chunk3ParentPathCheck 5
    && tttLargeFiber72Block4Chunk3ParentPathCheck 6
    && tttLargeFiber72Block4Chunk3ParentPathCheck 7
    && tttLargeFiber72Block4Chunk3ParentPathCheck 8
    && tttLargeFiber72Block4Chunk3ParentPathCheck 9
    && tttLargeFiber72Block4Chunk3ParentPathCheck 10
    && tttLargeFiber72Block4Chunk3ParentPathCheck 11
    && tttLargeFiber72Block4Chunk3ParentPathCheck 12
    && tttLargeFiber72Block4Chunk3ParentPathCheck 13
    && tttLargeFiber72Block4Chunk3ParentPathCheck 14
    && tttLargeFiber72Block4Chunk3ParentPathCheck 15

theorem tttLargeFiber72Block4Chunk3ParentsAudit_ok :
    tttLargeFiber72Block4Chunk3ParentsAudit = true := by
  simp [tttLargeFiber72Block4Chunk3ParentsAudit,
    tttLargeFiber72Block4Chunk3ParentPath_0_ok,
    tttLargeFiber72Block4Chunk3ParentPath_1_ok,
    tttLargeFiber72Block4Chunk3ParentPath_2_ok,
    tttLargeFiber72Block4Chunk3ParentPath_3_ok,
    tttLargeFiber72Block4Chunk3ParentPath_4_ok,
    tttLargeFiber72Block4Chunk3ParentPath_5_ok,
    tttLargeFiber72Block4Chunk3ParentPath_6_ok,
    tttLargeFiber72Block4Chunk3ParentPath_7_ok,
    tttLargeFiber72Block4Chunk3ParentPath_8_ok,
    tttLargeFiber72Block4Chunk3ParentPath_9_ok,
    tttLargeFiber72Block4Chunk3ParentPath_10_ok,
    tttLargeFiber72Block4Chunk3ParentPath_11_ok,
    tttLargeFiber72Block4Chunk3ParentPath_12_ok,
    tttLargeFiber72Block4Chunk3ParentPath_13_ok,
    tttLargeFiber72Block4Chunk3ParentPath_14_ok,
    tttLargeFiber72Block4Chunk3ParentPath_15_ok]

def tttLargeFiber72Block4Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block4Chunk3SourcesCheck &&
    tttLargeFiber72Block4Chunk3RowsAudit &&
    tttLargeFiber72Block4Chunk3ParentMapAudit &&
    tttLargeFiber72Block4Chunk3ParentsAudit

theorem tttLargeFiber72Block4Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber72Block4Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block4Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block4Chunk3SourcesCheck_ok,
    tttLargeFiber72Block4Chunk3RowsAudit_ok,
    tttLargeFiber72Block4Chunk3ParentMapAudit_ok,
    tttLargeFiber72Block4Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block4Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
