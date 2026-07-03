import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 2 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block2Chunk2Sources : List Nat :=
  [   432, 433, 434, 435, 436, 437, 438, 439,
   440, 441, 442, 443, 444, 445, 446, 447]

def tttLargeFiber36Row160 : TripleComponentParentRow :=
  tripleRow 432 400 10 32 148 10 16 80
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row161 : TripleComponentParentRow :=
  tripleRow 433 401 10 32 149 10 16 81
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row162 : TripleComponentParentRow :=
  tripleRow 434 402 10 32 150 10 16 82
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber36Row163 : TripleComponentParentRow :=
  tripleRow 435 432 10 32 151 10 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row164 : TripleComponentParentRow :=
  tripleRow 436 432 10 32 164 10 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row165 : TripleComponentParentRow :=
  tripleRow 437 433 10 32 165 10 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row166 : TripleComponentParentRow :=
  tripleRow 438 406 10 32 166 10 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row167 : TripleComponentParentRow :=
  tripleRow 439 407 10 32 167 10 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row168 : TripleComponentParentRow :=
  tripleRow 440 408 10 33 156 10 17 88
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row169 : TripleComponentParentRow :=
  tripleRow 441 409 10 33 157 10 17 89
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row170 : TripleComponentParentRow :=
  tripleRow 442 410 10 33 158 10 17 90
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber36Row171 : TripleComponentParentRow :=
  tripleRow 443 440 10 33 159 10 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row172 : TripleComponentParentRow :=
  tripleRow 444 440 10 33 172 10 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row173 : TripleComponentParentRow :=
  tripleRow 445 441 10 33 173 10 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row174 : TripleComponentParentRow :=
  tripleRow 446 414 10 33 174 10 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row175 : TripleComponentParentRow :=
  tripleRow 447 415 10 33 175 10 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row160
  , tttLargeFiber36Row161
  , tttLargeFiber36Row162
  , tttLargeFiber36Row163
  , tttLargeFiber36Row164
  , tttLargeFiber36Row165
  , tttLargeFiber36Row166
  , tttLargeFiber36Row167
  , tttLargeFiber36Row168
  , tttLargeFiber36Row169
  , tttLargeFiber36Row170
  , tttLargeFiber36Row171
  , tttLargeFiber36Row172
  , tttLargeFiber36Row173
  , tttLargeFiber36Row174
  , tttLargeFiber36Row175
  ]

def tttLargeFiber36Block2Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block2Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block2Chunk2ExpectedContains row.source &&
    tttLargeFiber36Block2Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber36Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber36Block2Chunk2Sources

theorem tttLargeFiber36Block2Chunk2SourcesCheck_ok :
    tttLargeFiber36Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber36Block2Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block2Chunk2RowValid
    (listGetD tttLargeFiber36Block2Chunk2Rows i default)

def tttLargeFiber36Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block2Chunk2Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block2Chunk2Sources 0 0 == 432
      && tttLargeFiber36ParentOf 432 == 400
      && tttLargeFiber36ParentOf 400 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block2Chunk2Sources 1 0 == 433
      && tttLargeFiber36ParentOf 433 == 401
      && tttLargeFiber36ParentOf 401 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block2Chunk2Sources 2 0 == 434
      && tttLargeFiber36ParentOf 434 == 402
      && tttLargeFiber36ParentOf 402 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block2Chunk2Sources 3 0 == 435
      && tttLargeFiber36ParentOf 435 == 432
      && tttLargeFiber36ParentOf 432 == 400
      && tttLargeFiber36ParentOf 400 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block2Chunk2Sources 4 0 == 436
      && tttLargeFiber36ParentOf 436 == 432
      && tttLargeFiber36ParentOf 432 == 400
      && tttLargeFiber36ParentOf 400 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block2Chunk2Sources 5 0 == 437
      && tttLargeFiber36ParentOf 437 == 433
      && tttLargeFiber36ParentOf 433 == 401
      && tttLargeFiber36ParentOf 401 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block2Chunk2Sources 6 0 == 438
      && tttLargeFiber36ParentOf 438 == 406
      && tttLargeFiber36ParentOf 406 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block2Chunk2Sources 7 0 == 439
      && tttLargeFiber36ParentOf 439 == 407
      && tttLargeFiber36ParentOf 407 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block2Chunk2Sources 8 0 == 440
      && tttLargeFiber36ParentOf 440 == 408
      && tttLargeFiber36ParentOf 408 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block2Chunk2Sources 9 0 == 441
      && tttLargeFiber36ParentOf 441 == 409
      && tttLargeFiber36ParentOf 409 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block2Chunk2Sources 10 0 == 442
      && tttLargeFiber36ParentOf 442 == 410
      && tttLargeFiber36ParentOf 410 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block2Chunk2Sources 11 0 == 443
      && tttLargeFiber36ParentOf 443 == 440
      && tttLargeFiber36ParentOf 440 == 408
      && tttLargeFiber36ParentOf 408 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block2Chunk2Sources 12 0 == 444
      && tttLargeFiber36ParentOf 444 == 440
      && tttLargeFiber36ParentOf 440 == 408
      && tttLargeFiber36ParentOf 408 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block2Chunk2Sources 13 0 == 445
      && tttLargeFiber36ParentOf 445 == 441
      && tttLargeFiber36ParentOf 441 == 409
      && tttLargeFiber36ParentOf 409 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block2Chunk2Sources 14 0 == 446
      && tttLargeFiber36ParentOf 446 == 414
      && tttLargeFiber36ParentOf 414 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block2Chunk2Sources 15 0 == 447
      && tttLargeFiber36ParentOf 447 == 415
      && tttLargeFiber36ParentOf 415 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block2Chunk2Row_0_ok :
    tttLargeFiber36Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_1_ok :
    tttLargeFiber36Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_2_ok :
    tttLargeFiber36Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_3_ok :
    tttLargeFiber36Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_4_ok :
    tttLargeFiber36Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_5_ok :
    tttLargeFiber36Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_6_ok :
    tttLargeFiber36Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_7_ok :
    tttLargeFiber36Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_8_ok :
    tttLargeFiber36Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_9_ok :
    tttLargeFiber36Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_10_ok :
    tttLargeFiber36Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_11_ok :
    tttLargeFiber36Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_12_ok :
    tttLargeFiber36Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_13_ok :
    tttLargeFiber36Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_14_ok :
    tttLargeFiber36Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2Row_15_ok :
    tttLargeFiber36Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_0_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_1_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_2_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_3_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_4_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_5_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_6_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_7_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_8_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_9_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_10_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_11_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_12_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_13_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_14_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentMap_15_ok :
    tttLargeFiber36Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_0_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_1_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_2_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_3_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_4_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_5_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_6_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_7_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_8_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_9_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_10_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_11_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_12_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_13_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_14_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block2Chunk2ParentPath_15_ok :
    tttLargeFiber36Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber36Block2Chunk2RowCheck 0
    && tttLargeFiber36Block2Chunk2RowCheck 1
    && tttLargeFiber36Block2Chunk2RowCheck 2
    && tttLargeFiber36Block2Chunk2RowCheck 3
    && tttLargeFiber36Block2Chunk2RowCheck 4
    && tttLargeFiber36Block2Chunk2RowCheck 5
    && tttLargeFiber36Block2Chunk2RowCheck 6
    && tttLargeFiber36Block2Chunk2RowCheck 7
    && tttLargeFiber36Block2Chunk2RowCheck 8
    && tttLargeFiber36Block2Chunk2RowCheck 9
    && tttLargeFiber36Block2Chunk2RowCheck 10
    && tttLargeFiber36Block2Chunk2RowCheck 11
    && tttLargeFiber36Block2Chunk2RowCheck 12
    && tttLargeFiber36Block2Chunk2RowCheck 13
    && tttLargeFiber36Block2Chunk2RowCheck 14
    && tttLargeFiber36Block2Chunk2RowCheck 15

theorem tttLargeFiber36Block2Chunk2RowsAudit_ok :
    tttLargeFiber36Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber36Block2Chunk2RowsAudit,
    tttLargeFiber36Block2Chunk2Row_0_ok,
    tttLargeFiber36Block2Chunk2Row_1_ok,
    tttLargeFiber36Block2Chunk2Row_2_ok,
    tttLargeFiber36Block2Chunk2Row_3_ok,
    tttLargeFiber36Block2Chunk2Row_4_ok,
    tttLargeFiber36Block2Chunk2Row_5_ok,
    tttLargeFiber36Block2Chunk2Row_6_ok,
    tttLargeFiber36Block2Chunk2Row_7_ok,
    tttLargeFiber36Block2Chunk2Row_8_ok,
    tttLargeFiber36Block2Chunk2Row_9_ok,
    tttLargeFiber36Block2Chunk2Row_10_ok,
    tttLargeFiber36Block2Chunk2Row_11_ok,
    tttLargeFiber36Block2Chunk2Row_12_ok,
    tttLargeFiber36Block2Chunk2Row_13_ok,
    tttLargeFiber36Block2Chunk2Row_14_ok,
    tttLargeFiber36Block2Chunk2Row_15_ok]

def tttLargeFiber36Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber36Block2Chunk2ParentMapCheck 0
    && tttLargeFiber36Block2Chunk2ParentMapCheck 1
    && tttLargeFiber36Block2Chunk2ParentMapCheck 2
    && tttLargeFiber36Block2Chunk2ParentMapCheck 3
    && tttLargeFiber36Block2Chunk2ParentMapCheck 4
    && tttLargeFiber36Block2Chunk2ParentMapCheck 5
    && tttLargeFiber36Block2Chunk2ParentMapCheck 6
    && tttLargeFiber36Block2Chunk2ParentMapCheck 7
    && tttLargeFiber36Block2Chunk2ParentMapCheck 8
    && tttLargeFiber36Block2Chunk2ParentMapCheck 9
    && tttLargeFiber36Block2Chunk2ParentMapCheck 10
    && tttLargeFiber36Block2Chunk2ParentMapCheck 11
    && tttLargeFiber36Block2Chunk2ParentMapCheck 12
    && tttLargeFiber36Block2Chunk2ParentMapCheck 13
    && tttLargeFiber36Block2Chunk2ParentMapCheck 14
    && tttLargeFiber36Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber36Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber36Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber36Block2Chunk2ParentMapAudit,
    tttLargeFiber36Block2Chunk2ParentMap_0_ok,
    tttLargeFiber36Block2Chunk2ParentMap_1_ok,
    tttLargeFiber36Block2Chunk2ParentMap_2_ok,
    tttLargeFiber36Block2Chunk2ParentMap_3_ok,
    tttLargeFiber36Block2Chunk2ParentMap_4_ok,
    tttLargeFiber36Block2Chunk2ParentMap_5_ok,
    tttLargeFiber36Block2Chunk2ParentMap_6_ok,
    tttLargeFiber36Block2Chunk2ParentMap_7_ok,
    tttLargeFiber36Block2Chunk2ParentMap_8_ok,
    tttLargeFiber36Block2Chunk2ParentMap_9_ok,
    tttLargeFiber36Block2Chunk2ParentMap_10_ok,
    tttLargeFiber36Block2Chunk2ParentMap_11_ok,
    tttLargeFiber36Block2Chunk2ParentMap_12_ok,
    tttLargeFiber36Block2Chunk2ParentMap_13_ok,
    tttLargeFiber36Block2Chunk2ParentMap_14_ok,
    tttLargeFiber36Block2Chunk2ParentMap_15_ok]

def tttLargeFiber36Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber36Block2Chunk2ParentPathCheck 0
    && tttLargeFiber36Block2Chunk2ParentPathCheck 1
    && tttLargeFiber36Block2Chunk2ParentPathCheck 2
    && tttLargeFiber36Block2Chunk2ParentPathCheck 3
    && tttLargeFiber36Block2Chunk2ParentPathCheck 4
    && tttLargeFiber36Block2Chunk2ParentPathCheck 5
    && tttLargeFiber36Block2Chunk2ParentPathCheck 6
    && tttLargeFiber36Block2Chunk2ParentPathCheck 7
    && tttLargeFiber36Block2Chunk2ParentPathCheck 8
    && tttLargeFiber36Block2Chunk2ParentPathCheck 9
    && tttLargeFiber36Block2Chunk2ParentPathCheck 10
    && tttLargeFiber36Block2Chunk2ParentPathCheck 11
    && tttLargeFiber36Block2Chunk2ParentPathCheck 12
    && tttLargeFiber36Block2Chunk2ParentPathCheck 13
    && tttLargeFiber36Block2Chunk2ParentPathCheck 14
    && tttLargeFiber36Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber36Block2Chunk2ParentsAudit_ok :
    tttLargeFiber36Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber36Block2Chunk2ParentsAudit,
    tttLargeFiber36Block2Chunk2ParentPath_0_ok,
    tttLargeFiber36Block2Chunk2ParentPath_1_ok,
    tttLargeFiber36Block2Chunk2ParentPath_2_ok,
    tttLargeFiber36Block2Chunk2ParentPath_3_ok,
    tttLargeFiber36Block2Chunk2ParentPath_4_ok,
    tttLargeFiber36Block2Chunk2ParentPath_5_ok,
    tttLargeFiber36Block2Chunk2ParentPath_6_ok,
    tttLargeFiber36Block2Chunk2ParentPath_7_ok,
    tttLargeFiber36Block2Chunk2ParentPath_8_ok,
    tttLargeFiber36Block2Chunk2ParentPath_9_ok,
    tttLargeFiber36Block2Chunk2ParentPath_10_ok,
    tttLargeFiber36Block2Chunk2ParentPath_11_ok,
    tttLargeFiber36Block2Chunk2ParentPath_12_ok,
    tttLargeFiber36Block2Chunk2ParentPath_13_ok,
    tttLargeFiber36Block2Chunk2ParentPath_14_ok,
    tttLargeFiber36Block2Chunk2ParentPath_15_ok]

def tttLargeFiber36Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block2Chunk2SourcesCheck &&
    tttLargeFiber36Block2Chunk2RowsAudit &&
    tttLargeFiber36Block2Chunk2ParentMapAudit &&
    tttLargeFiber36Block2Chunk2ParentsAudit

theorem tttLargeFiber36Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber36Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block2Chunk2SourcesCheck_ok,
    tttLargeFiber36Block2Chunk2RowsAudit_ok,
    tttLargeFiber36Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber36Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
