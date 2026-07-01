import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 4 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block4Chunk0Sources : List Nat :=
  [   1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367,
   1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]

def tttLargeFiber72Row256 : TripleComponentParentRow :=
  tripleRow 1360 816 40 148 148 24 80 80
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

def tttLargeFiber72Row257 : TripleComponentParentRow :=
  tripleRow 1361 817 40 148 149 24 80 81
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

def tttLargeFiber72Row258 : TripleComponentParentRow :=
  tripleRow 1362 818 40 148 150 24 80 82
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

def tttLargeFiber72Row259 : TripleComponentParentRow :=
  tripleRow 1363 1360 40 148 151 40 148 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row260 : TripleComponentParentRow :=
  tripleRow 1364 1360 40 148 164 40 148 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row261 : TripleComponentParentRow :=
  tripleRow 1365 1361 40 148 165 40 148 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row262 : TripleComponentParentRow :=
  tripleRow 1366 822 40 148 166 24 80 102
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

def tttLargeFiber72Row263 : TripleComponentParentRow :=
  tripleRow 1367 823 40 148 167 24 80 103
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

def tttLargeFiber72Row264 : TripleComponentParentRow :=
  tripleRow 1368 824 40 149 156 24 81 88
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

def tttLargeFiber72Row265 : TripleComponentParentRow :=
  tripleRow 1369 825 40 149 157 24 81 89
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

def tttLargeFiber72Row266 : TripleComponentParentRow :=
  tripleRow 1370 826 40 149 158 24 81 90
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

def tttLargeFiber72Row267 : TripleComponentParentRow :=
  tripleRow 1371 1368 40 149 159 40 149 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row268 : TripleComponentParentRow :=
  tripleRow 1372 1368 40 149 172 40 149 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row269 : TripleComponentParentRow :=
  tripleRow 1373 1369 40 149 173 40 149 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row270 : TripleComponentParentRow :=
  tripleRow 1374 830 40 149 174 24 81 110
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

def tttLargeFiber72Row271 : TripleComponentParentRow :=
  tripleRow 1375 831 40 149 175 24 81 111
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

def tttLargeFiber72Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row256
  , tttLargeFiber72Row257
  , tttLargeFiber72Row258
  , tttLargeFiber72Row259
  , tttLargeFiber72Row260
  , tttLargeFiber72Row261
  , tttLargeFiber72Row262
  , tttLargeFiber72Row263
  , tttLargeFiber72Row264
  , tttLargeFiber72Row265
  , tttLargeFiber72Row266
  , tttLargeFiber72Row267
  , tttLargeFiber72Row268
  , tttLargeFiber72Row269
  , tttLargeFiber72Row270
  , tttLargeFiber72Row271
  ]

def tttLargeFiber72Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber72Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber72Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber72Block4Chunk0Sources

theorem tttLargeFiber72Block4Chunk0SourcesCheck_ok :
    tttLargeFiber72Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber72Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block4Chunk0RowValid
    (listGetD tttLargeFiber72Block4Chunk0Rows i default)

def tttLargeFiber72Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block4Chunk0Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block4Chunk0Sources 0 0 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (1 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block4Chunk0Sources 1 0 == 1361
      && tttLargeFiber72ParentOf 1361 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block4Chunk0Sources 2 0 == 1362
      && tttLargeFiber72ParentOf 1362 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block4Chunk0Sources 3 0 == 1363
      && tttLargeFiber72ParentOf 1363 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block4Chunk0Sources 4 0 == 1364
      && tttLargeFiber72ParentOf 1364 == 1360
      && tttLargeFiber72ParentOf 1360 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block4Chunk0Sources 5 0 == 1365
      && tttLargeFiber72ParentOf 1365 == 1361
      && tttLargeFiber72ParentOf 1361 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block4Chunk0Sources 6 0 == 1366
      && tttLargeFiber72ParentOf 1366 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block4Chunk0Sources 7 0 == 1367
      && tttLargeFiber72ParentOf 1367 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block4Chunk0Sources 8 0 == 1368
      && tttLargeFiber72ParentOf 1368 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block4Chunk0Sources 9 0 == 1369
      && tttLargeFiber72ParentOf 1369 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block4Chunk0Sources 10 0 == 1370
      && tttLargeFiber72ParentOf 1370 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block4Chunk0Sources 11 0 == 1371
      && tttLargeFiber72ParentOf 1371 == 1368
      && tttLargeFiber72ParentOf 1368 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block4Chunk0Sources 12 0 == 1372
      && tttLargeFiber72ParentOf 1372 == 1368
      && tttLargeFiber72ParentOf 1368 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block4Chunk0Sources 13 0 == 1373
      && tttLargeFiber72ParentOf 1373 == 1369
      && tttLargeFiber72ParentOf 1369 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block4Chunk0Sources 14 0 == 1374
      && tttLargeFiber72ParentOf 1374 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block4Chunk0Sources 15 0 == 1375
      && tttLargeFiber72ParentOf 1375 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block4Chunk0Row_0_ok :
    tttLargeFiber72Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_1_ok :
    tttLargeFiber72Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_2_ok :
    tttLargeFiber72Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_3_ok :
    tttLargeFiber72Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_4_ok :
    tttLargeFiber72Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_5_ok :
    tttLargeFiber72Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_6_ok :
    tttLargeFiber72Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_7_ok :
    tttLargeFiber72Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_8_ok :
    tttLargeFiber72Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_9_ok :
    tttLargeFiber72Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_10_ok :
    tttLargeFiber72Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_11_ok :
    tttLargeFiber72Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_12_ok :
    tttLargeFiber72Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_13_ok :
    tttLargeFiber72Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_14_ok :
    tttLargeFiber72Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0Row_15_ok :
    tttLargeFiber72Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_0_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_1_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_2_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_3_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_4_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_5_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_6_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_7_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_8_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_9_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_10_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_11_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_12_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_13_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_14_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentMap_15_ok :
    tttLargeFiber72Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_0_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_1_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_2_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_3_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_4_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_5_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_6_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_7_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_8_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_9_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_10_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_11_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_12_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_13_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_14_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block4Chunk0ParentPath_15_ok :
    tttLargeFiber72Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber72Block4Chunk0RowCheck 0
    && tttLargeFiber72Block4Chunk0RowCheck 1
    && tttLargeFiber72Block4Chunk0RowCheck 2
    && tttLargeFiber72Block4Chunk0RowCheck 3
    && tttLargeFiber72Block4Chunk0RowCheck 4
    && tttLargeFiber72Block4Chunk0RowCheck 5
    && tttLargeFiber72Block4Chunk0RowCheck 6
    && tttLargeFiber72Block4Chunk0RowCheck 7
    && tttLargeFiber72Block4Chunk0RowCheck 8
    && tttLargeFiber72Block4Chunk0RowCheck 9
    && tttLargeFiber72Block4Chunk0RowCheck 10
    && tttLargeFiber72Block4Chunk0RowCheck 11
    && tttLargeFiber72Block4Chunk0RowCheck 12
    && tttLargeFiber72Block4Chunk0RowCheck 13
    && tttLargeFiber72Block4Chunk0RowCheck 14
    && tttLargeFiber72Block4Chunk0RowCheck 15

theorem tttLargeFiber72Block4Chunk0RowsAudit_ok :
    tttLargeFiber72Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber72Block4Chunk0RowsAudit,
    tttLargeFiber72Block4Chunk0Row_0_ok,
    tttLargeFiber72Block4Chunk0Row_1_ok,
    tttLargeFiber72Block4Chunk0Row_2_ok,
    tttLargeFiber72Block4Chunk0Row_3_ok,
    tttLargeFiber72Block4Chunk0Row_4_ok,
    tttLargeFiber72Block4Chunk0Row_5_ok,
    tttLargeFiber72Block4Chunk0Row_6_ok,
    tttLargeFiber72Block4Chunk0Row_7_ok,
    tttLargeFiber72Block4Chunk0Row_8_ok,
    tttLargeFiber72Block4Chunk0Row_9_ok,
    tttLargeFiber72Block4Chunk0Row_10_ok,
    tttLargeFiber72Block4Chunk0Row_11_ok,
    tttLargeFiber72Block4Chunk0Row_12_ok,
    tttLargeFiber72Block4Chunk0Row_13_ok,
    tttLargeFiber72Block4Chunk0Row_14_ok,
    tttLargeFiber72Block4Chunk0Row_15_ok]

def tttLargeFiber72Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber72Block4Chunk0ParentMapCheck 0
    && tttLargeFiber72Block4Chunk0ParentMapCheck 1
    && tttLargeFiber72Block4Chunk0ParentMapCheck 2
    && tttLargeFiber72Block4Chunk0ParentMapCheck 3
    && tttLargeFiber72Block4Chunk0ParentMapCheck 4
    && tttLargeFiber72Block4Chunk0ParentMapCheck 5
    && tttLargeFiber72Block4Chunk0ParentMapCheck 6
    && tttLargeFiber72Block4Chunk0ParentMapCheck 7
    && tttLargeFiber72Block4Chunk0ParentMapCheck 8
    && tttLargeFiber72Block4Chunk0ParentMapCheck 9
    && tttLargeFiber72Block4Chunk0ParentMapCheck 10
    && tttLargeFiber72Block4Chunk0ParentMapCheck 11
    && tttLargeFiber72Block4Chunk0ParentMapCheck 12
    && tttLargeFiber72Block4Chunk0ParentMapCheck 13
    && tttLargeFiber72Block4Chunk0ParentMapCheck 14
    && tttLargeFiber72Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber72Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber72Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber72Block4Chunk0ParentMapAudit,
    tttLargeFiber72Block4Chunk0ParentMap_0_ok,
    tttLargeFiber72Block4Chunk0ParentMap_1_ok,
    tttLargeFiber72Block4Chunk0ParentMap_2_ok,
    tttLargeFiber72Block4Chunk0ParentMap_3_ok,
    tttLargeFiber72Block4Chunk0ParentMap_4_ok,
    tttLargeFiber72Block4Chunk0ParentMap_5_ok,
    tttLargeFiber72Block4Chunk0ParentMap_6_ok,
    tttLargeFiber72Block4Chunk0ParentMap_7_ok,
    tttLargeFiber72Block4Chunk0ParentMap_8_ok,
    tttLargeFiber72Block4Chunk0ParentMap_9_ok,
    tttLargeFiber72Block4Chunk0ParentMap_10_ok,
    tttLargeFiber72Block4Chunk0ParentMap_11_ok,
    tttLargeFiber72Block4Chunk0ParentMap_12_ok,
    tttLargeFiber72Block4Chunk0ParentMap_13_ok,
    tttLargeFiber72Block4Chunk0ParentMap_14_ok,
    tttLargeFiber72Block4Chunk0ParentMap_15_ok]

def tttLargeFiber72Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber72Block4Chunk0ParentPathCheck 0
    && tttLargeFiber72Block4Chunk0ParentPathCheck 1
    && tttLargeFiber72Block4Chunk0ParentPathCheck 2
    && tttLargeFiber72Block4Chunk0ParentPathCheck 3
    && tttLargeFiber72Block4Chunk0ParentPathCheck 4
    && tttLargeFiber72Block4Chunk0ParentPathCheck 5
    && tttLargeFiber72Block4Chunk0ParentPathCheck 6
    && tttLargeFiber72Block4Chunk0ParentPathCheck 7
    && tttLargeFiber72Block4Chunk0ParentPathCheck 8
    && tttLargeFiber72Block4Chunk0ParentPathCheck 9
    && tttLargeFiber72Block4Chunk0ParentPathCheck 10
    && tttLargeFiber72Block4Chunk0ParentPathCheck 11
    && tttLargeFiber72Block4Chunk0ParentPathCheck 12
    && tttLargeFiber72Block4Chunk0ParentPathCheck 13
    && tttLargeFiber72Block4Chunk0ParentPathCheck 14
    && tttLargeFiber72Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber72Block4Chunk0ParentsAudit_ok :
    tttLargeFiber72Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber72Block4Chunk0ParentsAudit,
    tttLargeFiber72Block4Chunk0ParentPath_0_ok,
    tttLargeFiber72Block4Chunk0ParentPath_1_ok,
    tttLargeFiber72Block4Chunk0ParentPath_2_ok,
    tttLargeFiber72Block4Chunk0ParentPath_3_ok,
    tttLargeFiber72Block4Chunk0ParentPath_4_ok,
    tttLargeFiber72Block4Chunk0ParentPath_5_ok,
    tttLargeFiber72Block4Chunk0ParentPath_6_ok,
    tttLargeFiber72Block4Chunk0ParentPath_7_ok,
    tttLargeFiber72Block4Chunk0ParentPath_8_ok,
    tttLargeFiber72Block4Chunk0ParentPath_9_ok,
    tttLargeFiber72Block4Chunk0ParentPath_10_ok,
    tttLargeFiber72Block4Chunk0ParentPath_11_ok,
    tttLargeFiber72Block4Chunk0ParentPath_12_ok,
    tttLargeFiber72Block4Chunk0ParentPath_13_ok,
    tttLargeFiber72Block4Chunk0ParentPath_14_ok,
    tttLargeFiber72Block4Chunk0ParentPath_15_ok]

def tttLargeFiber72Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block4Chunk0SourcesCheck &&
    tttLargeFiber72Block4Chunk0RowsAudit &&
    tttLargeFiber72Block4Chunk0ParentMapAudit &&
    tttLargeFiber72Block4Chunk0ParentsAudit

theorem tttLargeFiber72Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber72Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block4Chunk0SourcesCheck_ok,
    tttLargeFiber72Block4Chunk0RowsAudit_ok,
    tttLargeFiber72Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber72Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
