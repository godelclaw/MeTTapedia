import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 4 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block4Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block4Chunk1Sources : List Nat :=
  [   1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383,
   1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]

def tttLargeFiber72Row272 : TripleComponentParentRow :=
  tripleRow 1376 832 40 150 0 24 82 16
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

def tttLargeFiber72Row273 : TripleComponentParentRow :=
  tripleRow 1377 833 40 150 1 24 82 17
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

def tttLargeFiber72Row274 : TripleComponentParentRow :=
  tripleRow 1378 834 40 150 2 24 82 18
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

def tttLargeFiber72Row275 : TripleComponentParentRow :=
  tripleRow 1379 835 40 150 3 24 82 19
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

def tttLargeFiber72Row276 : TripleComponentParentRow :=
  tripleRow 1380 1368 40 150 48 40 149 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row277 : TripleComponentParentRow :=
  tripleRow 1381 1369 40 150 49 40 149 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row278 : TripleComponentParentRow :=
  tripleRow 1382 838 40 150 50 24 82 34
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

def tttLargeFiber72Row279 : TripleComponentParentRow :=
  tripleRow 1383 839 40 150 51 24 82 35
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

def tttLargeFiber72Row280 : TripleComponentParentRow :=
  tripleRow 1384 1367 40 151 8 40 148 167
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

def tttLargeFiber72Row281 : TripleComponentParentRow :=
  tripleRow 1385 1366 40 151 9 40 148 166
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

def tttLargeFiber72Row282 : TripleComponentParentRow :=
  tripleRow 1386 1364 40 151 10 40 148 164
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

def tttLargeFiber72Row283 : TripleComponentParentRow :=
  tripleRow 1387 1365 40 151 11 40 148 165
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

def tttLargeFiber72Row284 : TripleComponentParentRow :=
  tripleRow 1388 1360 40 151 56 40 148 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row285 : TripleComponentParentRow :=
  tripleRow 1389 1361 40 151 57 40 148 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row286 : TripleComponentParentRow :=
  tripleRow 1390 1362 40 151 58 40 148 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row287 : TripleComponentParentRow :=
  tripleRow 1391 1363 40 151 59 40 148 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Block4Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row272
  , tttLargeFiber72Row273
  , tttLargeFiber72Row274
  , tttLargeFiber72Row275
  , tttLargeFiber72Row276
  , tttLargeFiber72Row277
  , tttLargeFiber72Row278
  , tttLargeFiber72Row279
  , tttLargeFiber72Row280
  , tttLargeFiber72Row281
  , tttLargeFiber72Row282
  , tttLargeFiber72Row283
  , tttLargeFiber72Row284
  , tttLargeFiber72Row285
  , tttLargeFiber72Row286
  , tttLargeFiber72Row287
  ]

def tttLargeFiber72Block4Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block4Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block4Chunk1ExpectedContains row.source &&
    tttLargeFiber72Block4Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block4Chunk1SourcesCheck : Bool :=
  (tttLargeFiber72Block4Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber72Block4Chunk1Sources

theorem tttLargeFiber72Block4Chunk1SourcesCheck_ok :
    tttLargeFiber72Block4Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber72Block4Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block4Chunk1RowValid
    (listGetD tttLargeFiber72Block4Chunk1Rows i default)

def tttLargeFiber72Block4Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block4Chunk1Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block4Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block4Chunk1Sources 0 0 == 1376
      && tttLargeFiber72ParentOf 1376 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block4Chunk1Sources 1 0 == 1377
      && tttLargeFiber72ParentOf 1377 == 833
      && tttLargeFiber72ParentOf 833 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block4Chunk1Sources 2 0 == 1378
      && tttLargeFiber72ParentOf 1378 == 834
      && tttLargeFiber72ParentOf 834 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block4Chunk1Sources 3 0 == 1379
      && tttLargeFiber72ParentOf 1379 == 835
      && tttLargeFiber72ParentOf 835 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block4Chunk1Sources 4 0 == 1380
      && tttLargeFiber72ParentOf 1380 == 1368
      && tttLargeFiber72ParentOf 1368 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block4Chunk1Sources 5 0 == 1381
      && tttLargeFiber72ParentOf 1381 == 1369
      && tttLargeFiber72ParentOf 1369 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block4Chunk1Sources 6 0 == 1382
      && tttLargeFiber72ParentOf 1382 == 838
      && tttLargeFiber72ParentOf 838 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block4Chunk1Sources 7 0 == 1383
      && tttLargeFiber72ParentOf 1383 == 839
      && tttLargeFiber72ParentOf 839 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block4Chunk1Sources 8 0 == 1384
      && tttLargeFiber72ParentOf 1384 == 1367
      && tttLargeFiber72ParentOf 1367 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block4Chunk1Sources 9 0 == 1385
      && tttLargeFiber72ParentOf 1385 == 1366
      && tttLargeFiber72ParentOf 1366 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block4Chunk1Sources 10 0 == 1386
      && tttLargeFiber72ParentOf 1386 == 1364
      && tttLargeFiber72ParentOf 1364 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block4Chunk1Sources 11 0 == 1387
      && tttLargeFiber72ParentOf 1387 == 1365
      && tttLargeFiber72ParentOf 1365 == 1361
      && tttLargeFiber72ParentOf 1361 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block4Chunk1Sources 12 0 == 1388
      && tttLargeFiber72ParentOf 1388 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block4Chunk1Sources 13 0 == 1389
      && tttLargeFiber72ParentOf 1389 == 1361
      && tttLargeFiber72ParentOf 1361 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block4Chunk1Sources 14 0 == 1390
      && tttLargeFiber72ParentOf 1390 == 1362
      && tttLargeFiber72ParentOf 1362 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block4Chunk1Sources 15 0 == 1391
      && tttLargeFiber72ParentOf 1391 == 1363
      && tttLargeFiber72ParentOf 1363 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block4Chunk1Row_0_ok :
    tttLargeFiber72Block4Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_1_ok :
    tttLargeFiber72Block4Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_2_ok :
    tttLargeFiber72Block4Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_3_ok :
    tttLargeFiber72Block4Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_4_ok :
    tttLargeFiber72Block4Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_5_ok :
    tttLargeFiber72Block4Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_6_ok :
    tttLargeFiber72Block4Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_7_ok :
    tttLargeFiber72Block4Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_8_ok :
    tttLargeFiber72Block4Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_9_ok :
    tttLargeFiber72Block4Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_10_ok :
    tttLargeFiber72Block4Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_11_ok :
    tttLargeFiber72Block4Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_12_ok :
    tttLargeFiber72Block4Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_13_ok :
    tttLargeFiber72Block4Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_14_ok :
    tttLargeFiber72Block4Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1Row_15_ok :
    tttLargeFiber72Block4Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_0_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_1_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_2_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_3_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_4_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_5_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_6_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_7_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_8_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_9_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_10_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_11_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_12_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_13_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_14_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentMap_15_ok :
    tttLargeFiber72Block4Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_0_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_1_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_2_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_3_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_4_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_5_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_6_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_7_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_8_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_9_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_10_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_11_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_12_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_13_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_14_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk1ParentPath_15_ok :
    tttLargeFiber72Block4Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block4Chunk1RowsAudit : Bool :=
  tttLargeFiber72Block4Chunk1RowCheck 0
    && tttLargeFiber72Block4Chunk1RowCheck 1
    && tttLargeFiber72Block4Chunk1RowCheck 2
    && tttLargeFiber72Block4Chunk1RowCheck 3
    && tttLargeFiber72Block4Chunk1RowCheck 4
    && tttLargeFiber72Block4Chunk1RowCheck 5
    && tttLargeFiber72Block4Chunk1RowCheck 6
    && tttLargeFiber72Block4Chunk1RowCheck 7
    && tttLargeFiber72Block4Chunk1RowCheck 8
    && tttLargeFiber72Block4Chunk1RowCheck 9
    && tttLargeFiber72Block4Chunk1RowCheck 10
    && tttLargeFiber72Block4Chunk1RowCheck 11
    && tttLargeFiber72Block4Chunk1RowCheck 12
    && tttLargeFiber72Block4Chunk1RowCheck 13
    && tttLargeFiber72Block4Chunk1RowCheck 14
    && tttLargeFiber72Block4Chunk1RowCheck 15

theorem tttLargeFiber72Block4Chunk1RowsAudit_ok :
    tttLargeFiber72Block4Chunk1RowsAudit = true := by
  simp [tttLargeFiber72Block4Chunk1RowsAudit,
    tttLargeFiber72Block4Chunk1Row_0_ok,
    tttLargeFiber72Block4Chunk1Row_1_ok,
    tttLargeFiber72Block4Chunk1Row_2_ok,
    tttLargeFiber72Block4Chunk1Row_3_ok,
    tttLargeFiber72Block4Chunk1Row_4_ok,
    tttLargeFiber72Block4Chunk1Row_5_ok,
    tttLargeFiber72Block4Chunk1Row_6_ok,
    tttLargeFiber72Block4Chunk1Row_7_ok,
    tttLargeFiber72Block4Chunk1Row_8_ok,
    tttLargeFiber72Block4Chunk1Row_9_ok,
    tttLargeFiber72Block4Chunk1Row_10_ok,
    tttLargeFiber72Block4Chunk1Row_11_ok,
    tttLargeFiber72Block4Chunk1Row_12_ok,
    tttLargeFiber72Block4Chunk1Row_13_ok,
    tttLargeFiber72Block4Chunk1Row_14_ok,
    tttLargeFiber72Block4Chunk1Row_15_ok]

def tttLargeFiber72Block4Chunk1ParentMapAudit : Bool :=
  tttLargeFiber72Block4Chunk1ParentMapCheck 0
    && tttLargeFiber72Block4Chunk1ParentMapCheck 1
    && tttLargeFiber72Block4Chunk1ParentMapCheck 2
    && tttLargeFiber72Block4Chunk1ParentMapCheck 3
    && tttLargeFiber72Block4Chunk1ParentMapCheck 4
    && tttLargeFiber72Block4Chunk1ParentMapCheck 5
    && tttLargeFiber72Block4Chunk1ParentMapCheck 6
    && tttLargeFiber72Block4Chunk1ParentMapCheck 7
    && tttLargeFiber72Block4Chunk1ParentMapCheck 8
    && tttLargeFiber72Block4Chunk1ParentMapCheck 9
    && tttLargeFiber72Block4Chunk1ParentMapCheck 10
    && tttLargeFiber72Block4Chunk1ParentMapCheck 11
    && tttLargeFiber72Block4Chunk1ParentMapCheck 12
    && tttLargeFiber72Block4Chunk1ParentMapCheck 13
    && tttLargeFiber72Block4Chunk1ParentMapCheck 14
    && tttLargeFiber72Block4Chunk1ParentMapCheck 15

theorem tttLargeFiber72Block4Chunk1ParentMapAudit_ok :
    tttLargeFiber72Block4Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber72Block4Chunk1ParentMapAudit,
    tttLargeFiber72Block4Chunk1ParentMap_0_ok,
    tttLargeFiber72Block4Chunk1ParentMap_1_ok,
    tttLargeFiber72Block4Chunk1ParentMap_2_ok,
    tttLargeFiber72Block4Chunk1ParentMap_3_ok,
    tttLargeFiber72Block4Chunk1ParentMap_4_ok,
    tttLargeFiber72Block4Chunk1ParentMap_5_ok,
    tttLargeFiber72Block4Chunk1ParentMap_6_ok,
    tttLargeFiber72Block4Chunk1ParentMap_7_ok,
    tttLargeFiber72Block4Chunk1ParentMap_8_ok,
    tttLargeFiber72Block4Chunk1ParentMap_9_ok,
    tttLargeFiber72Block4Chunk1ParentMap_10_ok,
    tttLargeFiber72Block4Chunk1ParentMap_11_ok,
    tttLargeFiber72Block4Chunk1ParentMap_12_ok,
    tttLargeFiber72Block4Chunk1ParentMap_13_ok,
    tttLargeFiber72Block4Chunk1ParentMap_14_ok,
    tttLargeFiber72Block4Chunk1ParentMap_15_ok]

def tttLargeFiber72Block4Chunk1ParentsAudit : Bool :=
  tttLargeFiber72Block4Chunk1ParentPathCheck 0
    && tttLargeFiber72Block4Chunk1ParentPathCheck 1
    && tttLargeFiber72Block4Chunk1ParentPathCheck 2
    && tttLargeFiber72Block4Chunk1ParentPathCheck 3
    && tttLargeFiber72Block4Chunk1ParentPathCheck 4
    && tttLargeFiber72Block4Chunk1ParentPathCheck 5
    && tttLargeFiber72Block4Chunk1ParentPathCheck 6
    && tttLargeFiber72Block4Chunk1ParentPathCheck 7
    && tttLargeFiber72Block4Chunk1ParentPathCheck 8
    && tttLargeFiber72Block4Chunk1ParentPathCheck 9
    && tttLargeFiber72Block4Chunk1ParentPathCheck 10
    && tttLargeFiber72Block4Chunk1ParentPathCheck 11
    && tttLargeFiber72Block4Chunk1ParentPathCheck 12
    && tttLargeFiber72Block4Chunk1ParentPathCheck 13
    && tttLargeFiber72Block4Chunk1ParentPathCheck 14
    && tttLargeFiber72Block4Chunk1ParentPathCheck 15

theorem tttLargeFiber72Block4Chunk1ParentsAudit_ok :
    tttLargeFiber72Block4Chunk1ParentsAudit = true := by
  simp [tttLargeFiber72Block4Chunk1ParentsAudit,
    tttLargeFiber72Block4Chunk1ParentPath_0_ok,
    tttLargeFiber72Block4Chunk1ParentPath_1_ok,
    tttLargeFiber72Block4Chunk1ParentPath_2_ok,
    tttLargeFiber72Block4Chunk1ParentPath_3_ok,
    tttLargeFiber72Block4Chunk1ParentPath_4_ok,
    tttLargeFiber72Block4Chunk1ParentPath_5_ok,
    tttLargeFiber72Block4Chunk1ParentPath_6_ok,
    tttLargeFiber72Block4Chunk1ParentPath_7_ok,
    tttLargeFiber72Block4Chunk1ParentPath_8_ok,
    tttLargeFiber72Block4Chunk1ParentPath_9_ok,
    tttLargeFiber72Block4Chunk1ParentPath_10_ok,
    tttLargeFiber72Block4Chunk1ParentPath_11_ok,
    tttLargeFiber72Block4Chunk1ParentPath_12_ok,
    tttLargeFiber72Block4Chunk1ParentPath_13_ok,
    tttLargeFiber72Block4Chunk1ParentPath_14_ok,
    tttLargeFiber72Block4Chunk1ParentPath_15_ok]

def tttLargeFiber72Block4Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block4Chunk1SourcesCheck &&
    tttLargeFiber72Block4Chunk1RowsAudit &&
    tttLargeFiber72Block4Chunk1ParentMapAudit &&
    tttLargeFiber72Block4Chunk1ParentsAudit

theorem tttLargeFiber72Block4Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber72Block4Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block4Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block4Chunk1SourcesCheck_ok,
    tttLargeFiber72Block4Chunk1RowsAudit_ok,
    tttLargeFiber72Block4Chunk1ParentMapAudit_ok,
    tttLargeFiber72Block4Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block4Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
