import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 5 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block5Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block5Chunk0Sources : List Nat :=
  [   1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159,
   1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]

def tttLargeFiber60Row320 : TripleComponentParentRow :=
  tripleRow 1152 608 33 156 148 17 88 80
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

def tttLargeFiber60Row321 : TripleComponentParentRow :=
  tripleRow 1153 609 33 156 149 17 88 81
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

def tttLargeFiber60Row322 : TripleComponentParentRow :=
  tripleRow 1154 610 33 156 150 17 88 82
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

def tttLargeFiber60Row323 : TripleComponentParentRow :=
  tripleRow 1155 1152 33 156 151 33 156 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row324 : TripleComponentParentRow :=
  tripleRow 1156 1152 33 156 164 33 156 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row325 : TripleComponentParentRow :=
  tripleRow 1157 1153 33 156 165 33 156 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row326 : TripleComponentParentRow :=
  tripleRow 1158 614 33 156 166 17 88 102
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

def tttLargeFiber60Row327 : TripleComponentParentRow :=
  tripleRow 1159 615 33 156 167 17 88 103
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

def tttLargeFiber60Row328 : TripleComponentParentRow :=
  tripleRow 1160 616 33 157 156 17 89 88
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

def tttLargeFiber60Row329 : TripleComponentParentRow :=
  tripleRow 1161 617 33 157 157 17 89 89
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

def tttLargeFiber60Row330 : TripleComponentParentRow :=
  tripleRow 1162 618 33 157 158 17 89 90
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

def tttLargeFiber60Row331 : TripleComponentParentRow :=
  tripleRow 1163 1160 33 157 159 33 157 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row332 : TripleComponentParentRow :=
  tripleRow 1164 1160 33 157 172 33 157 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row333 : TripleComponentParentRow :=
  tripleRow 1165 1161 33 157 173 33 157 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row334 : TripleComponentParentRow :=
  tripleRow 1166 622 33 157 174 17 89 110
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

def tttLargeFiber60Row335 : TripleComponentParentRow :=
  tripleRow 1167 623 33 157 175 17 89 111
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

def tttLargeFiber60Block5Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row320
  , tttLargeFiber60Row321
  , tttLargeFiber60Row322
  , tttLargeFiber60Row323
  , tttLargeFiber60Row324
  , tttLargeFiber60Row325
  , tttLargeFiber60Row326
  , tttLargeFiber60Row327
  , tttLargeFiber60Row328
  , tttLargeFiber60Row329
  , tttLargeFiber60Row330
  , tttLargeFiber60Row331
  , tttLargeFiber60Row332
  , tttLargeFiber60Row333
  , tttLargeFiber60Row334
  , tttLargeFiber60Row335
  ]

def tttLargeFiber60Block5Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block5Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block5Chunk0ExpectedContains row.source &&
    tttLargeFiber60Block5Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block5Chunk0SourcesCheck : Bool :=
  (tttLargeFiber60Block5Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber60Block5Chunk0Sources

theorem tttLargeFiber60Block5Chunk0SourcesCheck_ok :
    tttLargeFiber60Block5Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber60Block5Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block5Chunk0RowValid
    (listGetD tttLargeFiber60Block5Chunk0Rows i default)

def tttLargeFiber60Block5Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block5Chunk0Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block5Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block5Chunk0Sources 0 0 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block5Chunk0Sources 1 0 == 1153
      && tttLargeFiber60ParentOf 1153 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block5Chunk0Sources 2 0 == 1154
      && tttLargeFiber60ParentOf 1154 == 610
      && tttLargeFiber60ParentOf 610 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block5Chunk0Sources 3 0 == 1155
      && tttLargeFiber60ParentOf 1155 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block5Chunk0Sources 4 0 == 1156
      && tttLargeFiber60ParentOf 1156 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block5Chunk0Sources 5 0 == 1157
      && tttLargeFiber60ParentOf 1157 == 1153
      && tttLargeFiber60ParentOf 1153 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block5Chunk0Sources 6 0 == 1158
      && tttLargeFiber60ParentOf 1158 == 614
      && tttLargeFiber60ParentOf 614 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block5Chunk0Sources 7 0 == 1159
      && tttLargeFiber60ParentOf 1159 == 615
      && tttLargeFiber60ParentOf 615 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block5Chunk0Sources 8 0 == 1160
      && tttLargeFiber60ParentOf 1160 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block5Chunk0Sources 9 0 == 1161
      && tttLargeFiber60ParentOf 1161 == 617
      && tttLargeFiber60ParentOf 617 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block5Chunk0Sources 10 0 == 1162
      && tttLargeFiber60ParentOf 1162 == 618
      && tttLargeFiber60ParentOf 618 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block5Chunk0Sources 11 0 == 1163
      && tttLargeFiber60ParentOf 1163 == 1160
      && tttLargeFiber60ParentOf 1160 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block5Chunk0Sources 12 0 == 1164
      && tttLargeFiber60ParentOf 1164 == 1160
      && tttLargeFiber60ParentOf 1160 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block5Chunk0Sources 13 0 == 1165
      && tttLargeFiber60ParentOf 1165 == 1161
      && tttLargeFiber60ParentOf 1161 == 617
      && tttLargeFiber60ParentOf 617 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block5Chunk0Sources 14 0 == 1166
      && tttLargeFiber60ParentOf 1166 == 622
      && tttLargeFiber60ParentOf 622 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block5Chunk0Sources 15 0 == 1167
      && tttLargeFiber60ParentOf 1167 == 623
      && tttLargeFiber60ParentOf 623 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block5Chunk0Row_0_ok :
    tttLargeFiber60Block5Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_1_ok :
    tttLargeFiber60Block5Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_2_ok :
    tttLargeFiber60Block5Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_3_ok :
    tttLargeFiber60Block5Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_4_ok :
    tttLargeFiber60Block5Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_5_ok :
    tttLargeFiber60Block5Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_6_ok :
    tttLargeFiber60Block5Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_7_ok :
    tttLargeFiber60Block5Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_8_ok :
    tttLargeFiber60Block5Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_9_ok :
    tttLargeFiber60Block5Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_10_ok :
    tttLargeFiber60Block5Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_11_ok :
    tttLargeFiber60Block5Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_12_ok :
    tttLargeFiber60Block5Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_13_ok :
    tttLargeFiber60Block5Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_14_ok :
    tttLargeFiber60Block5Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0Row_15_ok :
    tttLargeFiber60Block5Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_0_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_1_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_2_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_3_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_4_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_5_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_6_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_7_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_8_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_9_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_10_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_11_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_12_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_13_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_14_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentMap_15_ok :
    tttLargeFiber60Block5Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_0_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_1_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_2_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_3_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_4_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_5_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_6_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_7_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_8_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_9_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_10_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_11_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_12_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_13_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_14_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk0ParentPath_15_ok :
    tttLargeFiber60Block5Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block5Chunk0RowsAudit : Bool :=
  tttLargeFiber60Block5Chunk0RowCheck 0
    && tttLargeFiber60Block5Chunk0RowCheck 1
    && tttLargeFiber60Block5Chunk0RowCheck 2
    && tttLargeFiber60Block5Chunk0RowCheck 3
    && tttLargeFiber60Block5Chunk0RowCheck 4
    && tttLargeFiber60Block5Chunk0RowCheck 5
    && tttLargeFiber60Block5Chunk0RowCheck 6
    && tttLargeFiber60Block5Chunk0RowCheck 7
    && tttLargeFiber60Block5Chunk0RowCheck 8
    && tttLargeFiber60Block5Chunk0RowCheck 9
    && tttLargeFiber60Block5Chunk0RowCheck 10
    && tttLargeFiber60Block5Chunk0RowCheck 11
    && tttLargeFiber60Block5Chunk0RowCheck 12
    && tttLargeFiber60Block5Chunk0RowCheck 13
    && tttLargeFiber60Block5Chunk0RowCheck 14
    && tttLargeFiber60Block5Chunk0RowCheck 15

theorem tttLargeFiber60Block5Chunk0RowsAudit_ok :
    tttLargeFiber60Block5Chunk0RowsAudit = true := by
  simp [tttLargeFiber60Block5Chunk0RowsAudit,
    tttLargeFiber60Block5Chunk0Row_0_ok,
    tttLargeFiber60Block5Chunk0Row_1_ok,
    tttLargeFiber60Block5Chunk0Row_2_ok,
    tttLargeFiber60Block5Chunk0Row_3_ok,
    tttLargeFiber60Block5Chunk0Row_4_ok,
    tttLargeFiber60Block5Chunk0Row_5_ok,
    tttLargeFiber60Block5Chunk0Row_6_ok,
    tttLargeFiber60Block5Chunk0Row_7_ok,
    tttLargeFiber60Block5Chunk0Row_8_ok,
    tttLargeFiber60Block5Chunk0Row_9_ok,
    tttLargeFiber60Block5Chunk0Row_10_ok,
    tttLargeFiber60Block5Chunk0Row_11_ok,
    tttLargeFiber60Block5Chunk0Row_12_ok,
    tttLargeFiber60Block5Chunk0Row_13_ok,
    tttLargeFiber60Block5Chunk0Row_14_ok,
    tttLargeFiber60Block5Chunk0Row_15_ok]

def tttLargeFiber60Block5Chunk0ParentMapAudit : Bool :=
  tttLargeFiber60Block5Chunk0ParentMapCheck 0
    && tttLargeFiber60Block5Chunk0ParentMapCheck 1
    && tttLargeFiber60Block5Chunk0ParentMapCheck 2
    && tttLargeFiber60Block5Chunk0ParentMapCheck 3
    && tttLargeFiber60Block5Chunk0ParentMapCheck 4
    && tttLargeFiber60Block5Chunk0ParentMapCheck 5
    && tttLargeFiber60Block5Chunk0ParentMapCheck 6
    && tttLargeFiber60Block5Chunk0ParentMapCheck 7
    && tttLargeFiber60Block5Chunk0ParentMapCheck 8
    && tttLargeFiber60Block5Chunk0ParentMapCheck 9
    && tttLargeFiber60Block5Chunk0ParentMapCheck 10
    && tttLargeFiber60Block5Chunk0ParentMapCheck 11
    && tttLargeFiber60Block5Chunk0ParentMapCheck 12
    && tttLargeFiber60Block5Chunk0ParentMapCheck 13
    && tttLargeFiber60Block5Chunk0ParentMapCheck 14
    && tttLargeFiber60Block5Chunk0ParentMapCheck 15

theorem tttLargeFiber60Block5Chunk0ParentMapAudit_ok :
    tttLargeFiber60Block5Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber60Block5Chunk0ParentMapAudit,
    tttLargeFiber60Block5Chunk0ParentMap_0_ok,
    tttLargeFiber60Block5Chunk0ParentMap_1_ok,
    tttLargeFiber60Block5Chunk0ParentMap_2_ok,
    tttLargeFiber60Block5Chunk0ParentMap_3_ok,
    tttLargeFiber60Block5Chunk0ParentMap_4_ok,
    tttLargeFiber60Block5Chunk0ParentMap_5_ok,
    tttLargeFiber60Block5Chunk0ParentMap_6_ok,
    tttLargeFiber60Block5Chunk0ParentMap_7_ok,
    tttLargeFiber60Block5Chunk0ParentMap_8_ok,
    tttLargeFiber60Block5Chunk0ParentMap_9_ok,
    tttLargeFiber60Block5Chunk0ParentMap_10_ok,
    tttLargeFiber60Block5Chunk0ParentMap_11_ok,
    tttLargeFiber60Block5Chunk0ParentMap_12_ok,
    tttLargeFiber60Block5Chunk0ParentMap_13_ok,
    tttLargeFiber60Block5Chunk0ParentMap_14_ok,
    tttLargeFiber60Block5Chunk0ParentMap_15_ok]

def tttLargeFiber60Block5Chunk0ParentsAudit : Bool :=
  tttLargeFiber60Block5Chunk0ParentPathCheck 0
    && tttLargeFiber60Block5Chunk0ParentPathCheck 1
    && tttLargeFiber60Block5Chunk0ParentPathCheck 2
    && tttLargeFiber60Block5Chunk0ParentPathCheck 3
    && tttLargeFiber60Block5Chunk0ParentPathCheck 4
    && tttLargeFiber60Block5Chunk0ParentPathCheck 5
    && tttLargeFiber60Block5Chunk0ParentPathCheck 6
    && tttLargeFiber60Block5Chunk0ParentPathCheck 7
    && tttLargeFiber60Block5Chunk0ParentPathCheck 8
    && tttLargeFiber60Block5Chunk0ParentPathCheck 9
    && tttLargeFiber60Block5Chunk0ParentPathCheck 10
    && tttLargeFiber60Block5Chunk0ParentPathCheck 11
    && tttLargeFiber60Block5Chunk0ParentPathCheck 12
    && tttLargeFiber60Block5Chunk0ParentPathCheck 13
    && tttLargeFiber60Block5Chunk0ParentPathCheck 14
    && tttLargeFiber60Block5Chunk0ParentPathCheck 15

theorem tttLargeFiber60Block5Chunk0ParentsAudit_ok :
    tttLargeFiber60Block5Chunk0ParentsAudit = true := by
  simp [tttLargeFiber60Block5Chunk0ParentsAudit,
    tttLargeFiber60Block5Chunk0ParentPath_0_ok,
    tttLargeFiber60Block5Chunk0ParentPath_1_ok,
    tttLargeFiber60Block5Chunk0ParentPath_2_ok,
    tttLargeFiber60Block5Chunk0ParentPath_3_ok,
    tttLargeFiber60Block5Chunk0ParentPath_4_ok,
    tttLargeFiber60Block5Chunk0ParentPath_5_ok,
    tttLargeFiber60Block5Chunk0ParentPath_6_ok,
    tttLargeFiber60Block5Chunk0ParentPath_7_ok,
    tttLargeFiber60Block5Chunk0ParentPath_8_ok,
    tttLargeFiber60Block5Chunk0ParentPath_9_ok,
    tttLargeFiber60Block5Chunk0ParentPath_10_ok,
    tttLargeFiber60Block5Chunk0ParentPath_11_ok,
    tttLargeFiber60Block5Chunk0ParentPath_12_ok,
    tttLargeFiber60Block5Chunk0ParentPath_13_ok,
    tttLargeFiber60Block5Chunk0ParentPath_14_ok,
    tttLargeFiber60Block5Chunk0ParentPath_15_ok]

def tttLargeFiber60Block5Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block5Chunk0SourcesCheck &&
    tttLargeFiber60Block5Chunk0RowsAudit &&
    tttLargeFiber60Block5Chunk0ParentMapAudit &&
    tttLargeFiber60Block5Chunk0ParentsAudit

theorem tttLargeFiber60Block5Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber60Block5Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block5Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block5Chunk0SourcesCheck_ok,
    tttLargeFiber60Block5Chunk0RowsAudit_ok,
    tttLargeFiber60Block5Chunk0ParentMapAudit_ok,
    tttLargeFiber60Block5Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block5Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
