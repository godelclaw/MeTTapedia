import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 4 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block4Chunk0Sources : List Nat :=
  [   1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095,
   1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]

def tttLargeFiber60Row256 : TripleComponentParentRow :=
  tripleRow 1088 544 32 148 148 16 80 80
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

def tttLargeFiber60Row257 : TripleComponentParentRow :=
  tripleRow 1089 545 32 148 149 16 80 81
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

def tttLargeFiber60Row258 : TripleComponentParentRow :=
  tripleRow 1090 546 32 148 150 16 80 82
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

def tttLargeFiber60Row259 : TripleComponentParentRow :=
  tripleRow 1091 1088 32 148 151 32 148 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row260 : TripleComponentParentRow :=
  tripleRow 1092 1088 32 148 164 32 148 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row261 : TripleComponentParentRow :=
  tripleRow 1093 1089 32 148 165 32 148 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row262 : TripleComponentParentRow :=
  tripleRow 1094 550 32 148 166 16 80 102
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

def tttLargeFiber60Row263 : TripleComponentParentRow :=
  tripleRow 1095 551 32 148 167 16 80 103
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

def tttLargeFiber60Row264 : TripleComponentParentRow :=
  tripleRow 1096 552 32 149 156 16 81 88
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

def tttLargeFiber60Row265 : TripleComponentParentRow :=
  tripleRow 1097 553 32 149 157 16 81 89
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

def tttLargeFiber60Row266 : TripleComponentParentRow :=
  tripleRow 1098 554 32 149 158 16 81 90
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

def tttLargeFiber60Row267 : TripleComponentParentRow :=
  tripleRow 1099 1096 32 149 159 32 149 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row268 : TripleComponentParentRow :=
  tripleRow 1100 1096 32 149 172 32 149 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row269 : TripleComponentParentRow :=
  tripleRow 1101 1097 32 149 173 32 149 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row270 : TripleComponentParentRow :=
  tripleRow 1102 558 32 149 174 16 81 110
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

def tttLargeFiber60Row271 : TripleComponentParentRow :=
  tripleRow 1103 559 32 149 175 16 81 111
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

def tttLargeFiber60Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row256
  , tttLargeFiber60Row257
  , tttLargeFiber60Row258
  , tttLargeFiber60Row259
  , tttLargeFiber60Row260
  , tttLargeFiber60Row261
  , tttLargeFiber60Row262
  , tttLargeFiber60Row263
  , tttLargeFiber60Row264
  , tttLargeFiber60Row265
  , tttLargeFiber60Row266
  , tttLargeFiber60Row267
  , tttLargeFiber60Row268
  , tttLargeFiber60Row269
  , tttLargeFiber60Row270
  , tttLargeFiber60Row271
  ]

def tttLargeFiber60Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber60Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber60Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber60Block4Chunk0Sources

theorem tttLargeFiber60Block4Chunk0SourcesCheck_ok :
    tttLargeFiber60Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber60Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block4Chunk0RowValid
    (listGetD tttLargeFiber60Block4Chunk0Rows i default)

def tttLargeFiber60Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block4Chunk0Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block4Chunk0Sources 0 0 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (1 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block4Chunk0Sources 1 0 == 1089
      && tttLargeFiber60ParentOf 1089 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block4Chunk0Sources 2 0 == 1090
      && tttLargeFiber60ParentOf 1090 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block4Chunk0Sources 3 0 == 1091
      && tttLargeFiber60ParentOf 1091 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block4Chunk0Sources 4 0 == 1092
      && tttLargeFiber60ParentOf 1092 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block4Chunk0Sources 5 0 == 1093
      && tttLargeFiber60ParentOf 1093 == 1089
      && tttLargeFiber60ParentOf 1089 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block4Chunk0Sources 6 0 == 1094
      && tttLargeFiber60ParentOf 1094 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block4Chunk0Sources 7 0 == 1095
      && tttLargeFiber60ParentOf 1095 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block4Chunk0Sources 8 0 == 1096
      && tttLargeFiber60ParentOf 1096 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block4Chunk0Sources 9 0 == 1097
      && tttLargeFiber60ParentOf 1097 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block4Chunk0Sources 10 0 == 1098
      && tttLargeFiber60ParentOf 1098 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block4Chunk0Sources 11 0 == 1099
      && tttLargeFiber60ParentOf 1099 == 1096
      && tttLargeFiber60ParentOf 1096 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block4Chunk0Sources 12 0 == 1100
      && tttLargeFiber60ParentOf 1100 == 1096
      && tttLargeFiber60ParentOf 1096 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block4Chunk0Sources 13 0 == 1101
      && tttLargeFiber60ParentOf 1101 == 1097
      && tttLargeFiber60ParentOf 1097 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block4Chunk0Sources 14 0 == 1102
      && tttLargeFiber60ParentOf 1102 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block4Chunk0Sources 15 0 == 1103
      && tttLargeFiber60ParentOf 1103 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block4Chunk0Row_0_ok :
    tttLargeFiber60Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_1_ok :
    tttLargeFiber60Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_2_ok :
    tttLargeFiber60Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_3_ok :
    tttLargeFiber60Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_4_ok :
    tttLargeFiber60Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_5_ok :
    tttLargeFiber60Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_6_ok :
    tttLargeFiber60Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_7_ok :
    tttLargeFiber60Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_8_ok :
    tttLargeFiber60Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_9_ok :
    tttLargeFiber60Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_10_ok :
    tttLargeFiber60Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_11_ok :
    tttLargeFiber60Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_12_ok :
    tttLargeFiber60Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_13_ok :
    tttLargeFiber60Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_14_ok :
    tttLargeFiber60Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0Row_15_ok :
    tttLargeFiber60Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_0_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_1_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_2_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_3_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_4_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_5_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_6_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_7_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_8_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_9_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_10_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_11_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_12_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_13_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_14_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentMap_15_ok :
    tttLargeFiber60Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_0_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_1_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_2_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_3_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_4_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_5_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_6_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_7_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_8_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_9_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_10_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_11_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_12_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_13_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_14_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk0ParentPath_15_ok :
    tttLargeFiber60Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber60Block4Chunk0RowCheck 0
    && tttLargeFiber60Block4Chunk0RowCheck 1
    && tttLargeFiber60Block4Chunk0RowCheck 2
    && tttLargeFiber60Block4Chunk0RowCheck 3
    && tttLargeFiber60Block4Chunk0RowCheck 4
    && tttLargeFiber60Block4Chunk0RowCheck 5
    && tttLargeFiber60Block4Chunk0RowCheck 6
    && tttLargeFiber60Block4Chunk0RowCheck 7
    && tttLargeFiber60Block4Chunk0RowCheck 8
    && tttLargeFiber60Block4Chunk0RowCheck 9
    && tttLargeFiber60Block4Chunk0RowCheck 10
    && tttLargeFiber60Block4Chunk0RowCheck 11
    && tttLargeFiber60Block4Chunk0RowCheck 12
    && tttLargeFiber60Block4Chunk0RowCheck 13
    && tttLargeFiber60Block4Chunk0RowCheck 14
    && tttLargeFiber60Block4Chunk0RowCheck 15

theorem tttLargeFiber60Block4Chunk0RowsAudit_ok :
    tttLargeFiber60Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber60Block4Chunk0RowsAudit,
    tttLargeFiber60Block4Chunk0Row_0_ok,
    tttLargeFiber60Block4Chunk0Row_1_ok,
    tttLargeFiber60Block4Chunk0Row_2_ok,
    tttLargeFiber60Block4Chunk0Row_3_ok,
    tttLargeFiber60Block4Chunk0Row_4_ok,
    tttLargeFiber60Block4Chunk0Row_5_ok,
    tttLargeFiber60Block4Chunk0Row_6_ok,
    tttLargeFiber60Block4Chunk0Row_7_ok,
    tttLargeFiber60Block4Chunk0Row_8_ok,
    tttLargeFiber60Block4Chunk0Row_9_ok,
    tttLargeFiber60Block4Chunk0Row_10_ok,
    tttLargeFiber60Block4Chunk0Row_11_ok,
    tttLargeFiber60Block4Chunk0Row_12_ok,
    tttLargeFiber60Block4Chunk0Row_13_ok,
    tttLargeFiber60Block4Chunk0Row_14_ok,
    tttLargeFiber60Block4Chunk0Row_15_ok]

def tttLargeFiber60Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber60Block4Chunk0ParentMapCheck 0
    && tttLargeFiber60Block4Chunk0ParentMapCheck 1
    && tttLargeFiber60Block4Chunk0ParentMapCheck 2
    && tttLargeFiber60Block4Chunk0ParentMapCheck 3
    && tttLargeFiber60Block4Chunk0ParentMapCheck 4
    && tttLargeFiber60Block4Chunk0ParentMapCheck 5
    && tttLargeFiber60Block4Chunk0ParentMapCheck 6
    && tttLargeFiber60Block4Chunk0ParentMapCheck 7
    && tttLargeFiber60Block4Chunk0ParentMapCheck 8
    && tttLargeFiber60Block4Chunk0ParentMapCheck 9
    && tttLargeFiber60Block4Chunk0ParentMapCheck 10
    && tttLargeFiber60Block4Chunk0ParentMapCheck 11
    && tttLargeFiber60Block4Chunk0ParentMapCheck 12
    && tttLargeFiber60Block4Chunk0ParentMapCheck 13
    && tttLargeFiber60Block4Chunk0ParentMapCheck 14
    && tttLargeFiber60Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber60Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber60Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber60Block4Chunk0ParentMapAudit,
    tttLargeFiber60Block4Chunk0ParentMap_0_ok,
    tttLargeFiber60Block4Chunk0ParentMap_1_ok,
    tttLargeFiber60Block4Chunk0ParentMap_2_ok,
    tttLargeFiber60Block4Chunk0ParentMap_3_ok,
    tttLargeFiber60Block4Chunk0ParentMap_4_ok,
    tttLargeFiber60Block4Chunk0ParentMap_5_ok,
    tttLargeFiber60Block4Chunk0ParentMap_6_ok,
    tttLargeFiber60Block4Chunk0ParentMap_7_ok,
    tttLargeFiber60Block4Chunk0ParentMap_8_ok,
    tttLargeFiber60Block4Chunk0ParentMap_9_ok,
    tttLargeFiber60Block4Chunk0ParentMap_10_ok,
    tttLargeFiber60Block4Chunk0ParentMap_11_ok,
    tttLargeFiber60Block4Chunk0ParentMap_12_ok,
    tttLargeFiber60Block4Chunk0ParentMap_13_ok,
    tttLargeFiber60Block4Chunk0ParentMap_14_ok,
    tttLargeFiber60Block4Chunk0ParentMap_15_ok]

def tttLargeFiber60Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber60Block4Chunk0ParentPathCheck 0
    && tttLargeFiber60Block4Chunk0ParentPathCheck 1
    && tttLargeFiber60Block4Chunk0ParentPathCheck 2
    && tttLargeFiber60Block4Chunk0ParentPathCheck 3
    && tttLargeFiber60Block4Chunk0ParentPathCheck 4
    && tttLargeFiber60Block4Chunk0ParentPathCheck 5
    && tttLargeFiber60Block4Chunk0ParentPathCheck 6
    && tttLargeFiber60Block4Chunk0ParentPathCheck 7
    && tttLargeFiber60Block4Chunk0ParentPathCheck 8
    && tttLargeFiber60Block4Chunk0ParentPathCheck 9
    && tttLargeFiber60Block4Chunk0ParentPathCheck 10
    && tttLargeFiber60Block4Chunk0ParentPathCheck 11
    && tttLargeFiber60Block4Chunk0ParentPathCheck 12
    && tttLargeFiber60Block4Chunk0ParentPathCheck 13
    && tttLargeFiber60Block4Chunk0ParentPathCheck 14
    && tttLargeFiber60Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber60Block4Chunk0ParentsAudit_ok :
    tttLargeFiber60Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber60Block4Chunk0ParentsAudit,
    tttLargeFiber60Block4Chunk0ParentPath_0_ok,
    tttLargeFiber60Block4Chunk0ParentPath_1_ok,
    tttLargeFiber60Block4Chunk0ParentPath_2_ok,
    tttLargeFiber60Block4Chunk0ParentPath_3_ok,
    tttLargeFiber60Block4Chunk0ParentPath_4_ok,
    tttLargeFiber60Block4Chunk0ParentPath_5_ok,
    tttLargeFiber60Block4Chunk0ParentPath_6_ok,
    tttLargeFiber60Block4Chunk0ParentPath_7_ok,
    tttLargeFiber60Block4Chunk0ParentPath_8_ok,
    tttLargeFiber60Block4Chunk0ParentPath_9_ok,
    tttLargeFiber60Block4Chunk0ParentPath_10_ok,
    tttLargeFiber60Block4Chunk0ParentPath_11_ok,
    tttLargeFiber60Block4Chunk0ParentPath_12_ok,
    tttLargeFiber60Block4Chunk0ParentPath_13_ok,
    tttLargeFiber60Block4Chunk0ParentPath_14_ok,
    tttLargeFiber60Block4Chunk0ParentPath_15_ok]

def tttLargeFiber60Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block4Chunk0SourcesCheck &&
    tttLargeFiber60Block4Chunk0RowsAudit &&
    tttLargeFiber60Block4Chunk0ParentMapAudit &&
    tttLargeFiber60Block4Chunk0ParentsAudit

theorem tttLargeFiber60Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber60Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block4Chunk0SourcesCheck_ok,
    tttLargeFiber60Block4Chunk0RowsAudit_ok,
    tttLargeFiber60Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber60Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
