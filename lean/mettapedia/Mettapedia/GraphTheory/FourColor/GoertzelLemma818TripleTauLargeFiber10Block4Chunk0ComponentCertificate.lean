import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 4 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block4Chunk0Sources : List Nat :=
  [   4096, 4097, 4098, 4099, 4100, 4101, 4102, 4103,
   4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111]

def tttLargeFiber10Row256 : TripleComponentParentRow :=
  tripleRow 4096 4224 124 132 148 126 64 80
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber10Row257 : TripleComponentParentRow :=
  tripleRow 4097 4225 124 132 149 126 64 81
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber10Row258 : TripleComponentParentRow :=
  tripleRow 4098 4226 124 132 150 126 64 82
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row259 : TripleComponentParentRow :=
  tripleRow 4099 4096 124 132 151 124 132 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row260 : TripleComponentParentRow :=
  tripleRow 4100 4096 124 132 164 124 132 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row261 : TripleComponentParentRow :=
  tripleRow 4101 4097 124 132 165 124 132 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row262 : TripleComponentParentRow :=
  tripleRow 4102 4230 124 132 166 126 64 102
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row263 : TripleComponentParentRow :=
  tripleRow 4103 4231 124 132 167 126 64 103
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row264 : TripleComponentParentRow :=
  tripleRow 4104 4232 124 133 156 126 65 88
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber10Row265 : TripleComponentParentRow :=
  tripleRow 4105 4233 124 133 157 126 65 89
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber10Row266 : TripleComponentParentRow :=
  tripleRow 4106 4234 124 133 158 126 65 90
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row267 : TripleComponentParentRow :=
  tripleRow 4107 4104 124 133 159 124 133 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row268 : TripleComponentParentRow :=
  tripleRow 4108 4104 124 133 172 124 133 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row269 : TripleComponentParentRow :=
  tripleRow 4109 4105 124 133 173 124 133 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row270 : TripleComponentParentRow :=
  tripleRow 4110 4238 124 133 174 126 65 110
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row271 : TripleComponentParentRow :=
  tripleRow 4111 4239 124 133 175 126 65 111
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row256
  , tttLargeFiber10Row257
  , tttLargeFiber10Row258
  , tttLargeFiber10Row259
  , tttLargeFiber10Row260
  , tttLargeFiber10Row261
  , tttLargeFiber10Row262
  , tttLargeFiber10Row263
  , tttLargeFiber10Row264
  , tttLargeFiber10Row265
  , tttLargeFiber10Row266
  , tttLargeFiber10Row267
  , tttLargeFiber10Row268
  , tttLargeFiber10Row269
  , tttLargeFiber10Row270
  , tttLargeFiber10Row271
  ]

def tttLargeFiber10Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber10Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber10Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber10Block4Chunk0Sources

theorem tttLargeFiber10Block4Chunk0SourcesCheck_ok :
    tttLargeFiber10Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber10Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block4Chunk0RowValid
    (listGetD tttLargeFiber10Block4Chunk0Rows i default)

def tttLargeFiber10Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block4Chunk0Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block4Chunk0Sources 0 0 == 4096
      && tttLargeFiber10ParentOf 4096 == 4224
      && tttLargeFiber10ParentOf 4224 == 2512
      && tttLargeFiber10ParentOf 2512 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block4Chunk0Sources 1 0 == 4097
      && tttLargeFiber10ParentOf 4097 == 4225
      && tttLargeFiber10ParentOf 4225 == 2513
      && tttLargeFiber10ParentOf 2513 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block4Chunk0Sources 2 0 == 4098
      && tttLargeFiber10ParentOf 4098 == 4226
      && tttLargeFiber10ParentOf 4226 == 2514
      && tttLargeFiber10ParentOf 2514 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block4Chunk0Sources 3 0 == 4099
      && tttLargeFiber10ParentOf 4099 == 4096
      && tttLargeFiber10ParentOf 4096 == 4224
      && tttLargeFiber10ParentOf 4224 == 2512
      && tttLargeFiber10ParentOf 2512 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block4Chunk0Sources 4 0 == 4100
      && tttLargeFiber10ParentOf 4100 == 4096
      && tttLargeFiber10ParentOf 4096 == 4224
      && tttLargeFiber10ParentOf 4224 == 2512
      && tttLargeFiber10ParentOf 2512 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block4Chunk0Sources 5 0 == 4101
      && tttLargeFiber10ParentOf 4101 == 4097
      && tttLargeFiber10ParentOf 4097 == 4225
      && tttLargeFiber10ParentOf 4225 == 2513
      && tttLargeFiber10ParentOf 2513 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block4Chunk0Sources 6 0 == 4102
      && tttLargeFiber10ParentOf 4102 == 4230
      && tttLargeFiber10ParentOf 4230 == 2518
      && tttLargeFiber10ParentOf 2518 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block4Chunk0Sources 7 0 == 4103
      && tttLargeFiber10ParentOf 4103 == 4231
      && tttLargeFiber10ParentOf 4231 == 2519
      && tttLargeFiber10ParentOf 2519 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block4Chunk0Sources 8 0 == 4104
      && tttLargeFiber10ParentOf 4104 == 4232
      && tttLargeFiber10ParentOf 4232 == 2520
      && tttLargeFiber10ParentOf 2520 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block4Chunk0Sources 9 0 == 4105
      && tttLargeFiber10ParentOf 4105 == 4233
      && tttLargeFiber10ParentOf 4233 == 2521
      && tttLargeFiber10ParentOf 2521 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block4Chunk0Sources 10 0 == 4106
      && tttLargeFiber10ParentOf 4106 == 4234
      && tttLargeFiber10ParentOf 4234 == 2522
      && tttLargeFiber10ParentOf 2522 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block4Chunk0Sources 11 0 == 4107
      && tttLargeFiber10ParentOf 4107 == 4104
      && tttLargeFiber10ParentOf 4104 == 4232
      && tttLargeFiber10ParentOf 4232 == 2520
      && tttLargeFiber10ParentOf 2520 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block4Chunk0Sources 12 0 == 4108
      && tttLargeFiber10ParentOf 4108 == 4104
      && tttLargeFiber10ParentOf 4104 == 4232
      && tttLargeFiber10ParentOf 4232 == 2520
      && tttLargeFiber10ParentOf 2520 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block4Chunk0Sources 13 0 == 4109
      && tttLargeFiber10ParentOf 4109 == 4105
      && tttLargeFiber10ParentOf 4105 == 4233
      && tttLargeFiber10ParentOf 4233 == 2521
      && tttLargeFiber10ParentOf 2521 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block4Chunk0Sources 14 0 == 4110
      && tttLargeFiber10ParentOf 4110 == 4238
      && tttLargeFiber10ParentOf 4238 == 2526
      && tttLargeFiber10ParentOf 2526 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block4Chunk0Sources 15 0 == 4111
      && tttLargeFiber10ParentOf 4111 == 4239
      && tttLargeFiber10ParentOf 4239 == 2527
      && tttLargeFiber10ParentOf 2527 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block4Chunk0Row_0_ok :
    tttLargeFiber10Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_1_ok :
    tttLargeFiber10Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_2_ok :
    tttLargeFiber10Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_3_ok :
    tttLargeFiber10Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_4_ok :
    tttLargeFiber10Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_5_ok :
    tttLargeFiber10Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_6_ok :
    tttLargeFiber10Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_7_ok :
    tttLargeFiber10Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_8_ok :
    tttLargeFiber10Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_9_ok :
    tttLargeFiber10Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_10_ok :
    tttLargeFiber10Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_11_ok :
    tttLargeFiber10Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_12_ok :
    tttLargeFiber10Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_13_ok :
    tttLargeFiber10Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_14_ok :
    tttLargeFiber10Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0Row_15_ok :
    tttLargeFiber10Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_0_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_1_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_2_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_3_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_4_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_5_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_6_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_7_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_8_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_9_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_10_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_11_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_12_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_13_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_14_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentMap_15_ok :
    tttLargeFiber10Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_0_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_1_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_2_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_3_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_4_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_5_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_6_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_7_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_8_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_9_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_10_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_11_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_12_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_13_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_14_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block4Chunk0ParentPath_15_ok :
    tttLargeFiber10Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber10Block4Chunk0RowCheck 0
    && tttLargeFiber10Block4Chunk0RowCheck 1
    && tttLargeFiber10Block4Chunk0RowCheck 2
    && tttLargeFiber10Block4Chunk0RowCheck 3
    && tttLargeFiber10Block4Chunk0RowCheck 4
    && tttLargeFiber10Block4Chunk0RowCheck 5
    && tttLargeFiber10Block4Chunk0RowCheck 6
    && tttLargeFiber10Block4Chunk0RowCheck 7
    && tttLargeFiber10Block4Chunk0RowCheck 8
    && tttLargeFiber10Block4Chunk0RowCheck 9
    && tttLargeFiber10Block4Chunk0RowCheck 10
    && tttLargeFiber10Block4Chunk0RowCheck 11
    && tttLargeFiber10Block4Chunk0RowCheck 12
    && tttLargeFiber10Block4Chunk0RowCheck 13
    && tttLargeFiber10Block4Chunk0RowCheck 14
    && tttLargeFiber10Block4Chunk0RowCheck 15

theorem tttLargeFiber10Block4Chunk0RowsAudit_ok :
    tttLargeFiber10Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber10Block4Chunk0RowsAudit,
    tttLargeFiber10Block4Chunk0Row_0_ok,
    tttLargeFiber10Block4Chunk0Row_1_ok,
    tttLargeFiber10Block4Chunk0Row_2_ok,
    tttLargeFiber10Block4Chunk0Row_3_ok,
    tttLargeFiber10Block4Chunk0Row_4_ok,
    tttLargeFiber10Block4Chunk0Row_5_ok,
    tttLargeFiber10Block4Chunk0Row_6_ok,
    tttLargeFiber10Block4Chunk0Row_7_ok,
    tttLargeFiber10Block4Chunk0Row_8_ok,
    tttLargeFiber10Block4Chunk0Row_9_ok,
    tttLargeFiber10Block4Chunk0Row_10_ok,
    tttLargeFiber10Block4Chunk0Row_11_ok,
    tttLargeFiber10Block4Chunk0Row_12_ok,
    tttLargeFiber10Block4Chunk0Row_13_ok,
    tttLargeFiber10Block4Chunk0Row_14_ok,
    tttLargeFiber10Block4Chunk0Row_15_ok]

def tttLargeFiber10Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber10Block4Chunk0ParentMapCheck 0
    && tttLargeFiber10Block4Chunk0ParentMapCheck 1
    && tttLargeFiber10Block4Chunk0ParentMapCheck 2
    && tttLargeFiber10Block4Chunk0ParentMapCheck 3
    && tttLargeFiber10Block4Chunk0ParentMapCheck 4
    && tttLargeFiber10Block4Chunk0ParentMapCheck 5
    && tttLargeFiber10Block4Chunk0ParentMapCheck 6
    && tttLargeFiber10Block4Chunk0ParentMapCheck 7
    && tttLargeFiber10Block4Chunk0ParentMapCheck 8
    && tttLargeFiber10Block4Chunk0ParentMapCheck 9
    && tttLargeFiber10Block4Chunk0ParentMapCheck 10
    && tttLargeFiber10Block4Chunk0ParentMapCheck 11
    && tttLargeFiber10Block4Chunk0ParentMapCheck 12
    && tttLargeFiber10Block4Chunk0ParentMapCheck 13
    && tttLargeFiber10Block4Chunk0ParentMapCheck 14
    && tttLargeFiber10Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber10Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber10Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber10Block4Chunk0ParentMapAudit,
    tttLargeFiber10Block4Chunk0ParentMap_0_ok,
    tttLargeFiber10Block4Chunk0ParentMap_1_ok,
    tttLargeFiber10Block4Chunk0ParentMap_2_ok,
    tttLargeFiber10Block4Chunk0ParentMap_3_ok,
    tttLargeFiber10Block4Chunk0ParentMap_4_ok,
    tttLargeFiber10Block4Chunk0ParentMap_5_ok,
    tttLargeFiber10Block4Chunk0ParentMap_6_ok,
    tttLargeFiber10Block4Chunk0ParentMap_7_ok,
    tttLargeFiber10Block4Chunk0ParentMap_8_ok,
    tttLargeFiber10Block4Chunk0ParentMap_9_ok,
    tttLargeFiber10Block4Chunk0ParentMap_10_ok,
    tttLargeFiber10Block4Chunk0ParentMap_11_ok,
    tttLargeFiber10Block4Chunk0ParentMap_12_ok,
    tttLargeFiber10Block4Chunk0ParentMap_13_ok,
    tttLargeFiber10Block4Chunk0ParentMap_14_ok,
    tttLargeFiber10Block4Chunk0ParentMap_15_ok]

def tttLargeFiber10Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber10Block4Chunk0ParentPathCheck 0
    && tttLargeFiber10Block4Chunk0ParentPathCheck 1
    && tttLargeFiber10Block4Chunk0ParentPathCheck 2
    && tttLargeFiber10Block4Chunk0ParentPathCheck 3
    && tttLargeFiber10Block4Chunk0ParentPathCheck 4
    && tttLargeFiber10Block4Chunk0ParentPathCheck 5
    && tttLargeFiber10Block4Chunk0ParentPathCheck 6
    && tttLargeFiber10Block4Chunk0ParentPathCheck 7
    && tttLargeFiber10Block4Chunk0ParentPathCheck 8
    && tttLargeFiber10Block4Chunk0ParentPathCheck 9
    && tttLargeFiber10Block4Chunk0ParentPathCheck 10
    && tttLargeFiber10Block4Chunk0ParentPathCheck 11
    && tttLargeFiber10Block4Chunk0ParentPathCheck 12
    && tttLargeFiber10Block4Chunk0ParentPathCheck 13
    && tttLargeFiber10Block4Chunk0ParentPathCheck 14
    && tttLargeFiber10Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber10Block4Chunk0ParentsAudit_ok :
    tttLargeFiber10Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber10Block4Chunk0ParentsAudit,
    tttLargeFiber10Block4Chunk0ParentPath_0_ok,
    tttLargeFiber10Block4Chunk0ParentPath_1_ok,
    tttLargeFiber10Block4Chunk0ParentPath_2_ok,
    tttLargeFiber10Block4Chunk0ParentPath_3_ok,
    tttLargeFiber10Block4Chunk0ParentPath_4_ok,
    tttLargeFiber10Block4Chunk0ParentPath_5_ok,
    tttLargeFiber10Block4Chunk0ParentPath_6_ok,
    tttLargeFiber10Block4Chunk0ParentPath_7_ok,
    tttLargeFiber10Block4Chunk0ParentPath_8_ok,
    tttLargeFiber10Block4Chunk0ParentPath_9_ok,
    tttLargeFiber10Block4Chunk0ParentPath_10_ok,
    tttLargeFiber10Block4Chunk0ParentPath_11_ok,
    tttLargeFiber10Block4Chunk0ParentPath_12_ok,
    tttLargeFiber10Block4Chunk0ParentPath_13_ok,
    tttLargeFiber10Block4Chunk0ParentPath_14_ok,
    tttLargeFiber10Block4Chunk0ParentPath_15_ok]

def tttLargeFiber10Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block4Chunk0SourcesCheck &&
    tttLargeFiber10Block4Chunk0RowsAudit &&
    tttLargeFiber10Block4Chunk0ParentMapAudit &&
    tttLargeFiber10Block4Chunk0ParentsAudit

theorem tttLargeFiber10Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber10Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block4Chunk0SourcesCheck_ok,
    tttLargeFiber10Block4Chunk0RowsAudit_ok,
    tttLargeFiber10Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber10Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
