import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block0Chunk1Sources : List Nat :=
  [   288, 289, 290, 291, 292, 293, 294, 295,
   296, 297, 298, 299, 300, 301, 302, 303]

def tttLargeFiber36Row16 : TripleComponentParentRow :=
  tripleRow 288 272 8 82 16 8 80 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row17 : TripleComponentParentRow :=
  tripleRow 289 273 8 82 17 8 80 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row18 : TripleComponentParentRow :=
  tripleRow 290 274 8 82 18 8 80 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row19 : TripleComponentParentRow :=
  tripleRow 291 275 8 82 19 8 80 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row20 : TripleComponentParentRow :=
  tripleRow 292 288 8 82 32 8 82 16
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row21 : TripleComponentParentRow :=
  tripleRow 293 289 8 82 33 8 82 17
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row22 : TripleComponentParentRow :=
  tripleRow 294 278 8 82 34 8 80 102
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row23 : TripleComponentParentRow :=
  tripleRow 295 279 8 82 35 8 80 103
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row24 : TripleComponentParentRow :=
  tripleRow 296 280 8 83 24 8 81 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row25 : TripleComponentParentRow :=
  tripleRow 297 281 8 83 25 8 81 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row26 : TripleComponentParentRow :=
  tripleRow 298 282 8 83 26 8 81 90
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row27 : TripleComponentParentRow :=
  tripleRow 299 283 8 83 27 8 81 91
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row28 : TripleComponentParentRow :=
  tripleRow 300 296 8 83 40 8 83 24
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row29 : TripleComponentParentRow :=
  tripleRow 301 297 8 83 41 8 83 25
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row30 : TripleComponentParentRow :=
  tripleRow 302 286 8 83 42 8 81 110
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row31 : TripleComponentParentRow :=
  tripleRow 303 287 8 83 43 8 81 111
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row16
  , tttLargeFiber36Row17
  , tttLargeFiber36Row18
  , tttLargeFiber36Row19
  , tttLargeFiber36Row20
  , tttLargeFiber36Row21
  , tttLargeFiber36Row22
  , tttLargeFiber36Row23
  , tttLargeFiber36Row24
  , tttLargeFiber36Row25
  , tttLargeFiber36Row26
  , tttLargeFiber36Row27
  , tttLargeFiber36Row28
  , tttLargeFiber36Row29
  , tttLargeFiber36Row30
  , tttLargeFiber36Row31
  ]

def tttLargeFiber36Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber36Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber36Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber36Block0Chunk1Sources

theorem tttLargeFiber36Block0Chunk1SourcesCheck_ok :
    tttLargeFiber36Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber36Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block0Chunk1RowValid
    (listGetD tttLargeFiber36Block0Chunk1Rows i default)

def tttLargeFiber36Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block0Chunk1Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block0Chunk1Sources 0 0 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (1 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block0Chunk1Sources 1 0 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block0Chunk1Sources 2 0 == 290
      && tttLargeFiber36ParentOf 290 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block0Chunk1Sources 3 0 == 291
      && tttLargeFiber36ParentOf 291 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block0Chunk1Sources 4 0 == 292
      && tttLargeFiber36ParentOf 292 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block0Chunk1Sources 5 0 == 293
      && tttLargeFiber36ParentOf 293 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block0Chunk1Sources 6 0 == 294
      && tttLargeFiber36ParentOf 294 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block0Chunk1Sources 7 0 == 295
      && tttLargeFiber36ParentOf 295 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block0Chunk1Sources 8 0 == 296
      && tttLargeFiber36ParentOf 296 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block0Chunk1Sources 9 0 == 297
      && tttLargeFiber36ParentOf 297 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block0Chunk1Sources 10 0 == 298
      && tttLargeFiber36ParentOf 298 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block0Chunk1Sources 11 0 == 299
      && tttLargeFiber36ParentOf 299 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block0Chunk1Sources 12 0 == 300
      && tttLargeFiber36ParentOf 300 == 296
      && tttLargeFiber36ParentOf 296 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block0Chunk1Sources 13 0 == 301
      && tttLargeFiber36ParentOf 301 == 297
      && tttLargeFiber36ParentOf 297 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block0Chunk1Sources 14 0 == 302
      && tttLargeFiber36ParentOf 302 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block0Chunk1Sources 15 0 == 303
      && tttLargeFiber36ParentOf 303 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block0Chunk1Row_0_ok :
    tttLargeFiber36Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_1_ok :
    tttLargeFiber36Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_2_ok :
    tttLargeFiber36Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_3_ok :
    tttLargeFiber36Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_4_ok :
    tttLargeFiber36Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_5_ok :
    tttLargeFiber36Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_6_ok :
    tttLargeFiber36Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_7_ok :
    tttLargeFiber36Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_8_ok :
    tttLargeFiber36Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_9_ok :
    tttLargeFiber36Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_10_ok :
    tttLargeFiber36Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_11_ok :
    tttLargeFiber36Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_12_ok :
    tttLargeFiber36Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_13_ok :
    tttLargeFiber36Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_14_ok :
    tttLargeFiber36Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1Row_15_ok :
    tttLargeFiber36Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_0_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_1_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_2_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_3_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_4_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_5_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_6_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_7_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_8_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_9_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_10_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_11_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_12_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_13_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_14_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentMap_15_ok :
    tttLargeFiber36Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_0_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_1_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_2_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_3_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_4_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_5_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_6_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_7_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_8_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_9_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_10_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_11_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_12_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_13_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_14_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk1ParentPath_15_ok :
    tttLargeFiber36Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber36Block0Chunk1RowCheck 0
    && tttLargeFiber36Block0Chunk1RowCheck 1
    && tttLargeFiber36Block0Chunk1RowCheck 2
    && tttLargeFiber36Block0Chunk1RowCheck 3
    && tttLargeFiber36Block0Chunk1RowCheck 4
    && tttLargeFiber36Block0Chunk1RowCheck 5
    && tttLargeFiber36Block0Chunk1RowCheck 6
    && tttLargeFiber36Block0Chunk1RowCheck 7
    && tttLargeFiber36Block0Chunk1RowCheck 8
    && tttLargeFiber36Block0Chunk1RowCheck 9
    && tttLargeFiber36Block0Chunk1RowCheck 10
    && tttLargeFiber36Block0Chunk1RowCheck 11
    && tttLargeFiber36Block0Chunk1RowCheck 12
    && tttLargeFiber36Block0Chunk1RowCheck 13
    && tttLargeFiber36Block0Chunk1RowCheck 14
    && tttLargeFiber36Block0Chunk1RowCheck 15

theorem tttLargeFiber36Block0Chunk1RowsAudit_ok :
    tttLargeFiber36Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber36Block0Chunk1RowsAudit,
    tttLargeFiber36Block0Chunk1Row_0_ok,
    tttLargeFiber36Block0Chunk1Row_1_ok,
    tttLargeFiber36Block0Chunk1Row_2_ok,
    tttLargeFiber36Block0Chunk1Row_3_ok,
    tttLargeFiber36Block0Chunk1Row_4_ok,
    tttLargeFiber36Block0Chunk1Row_5_ok,
    tttLargeFiber36Block0Chunk1Row_6_ok,
    tttLargeFiber36Block0Chunk1Row_7_ok,
    tttLargeFiber36Block0Chunk1Row_8_ok,
    tttLargeFiber36Block0Chunk1Row_9_ok,
    tttLargeFiber36Block0Chunk1Row_10_ok,
    tttLargeFiber36Block0Chunk1Row_11_ok,
    tttLargeFiber36Block0Chunk1Row_12_ok,
    tttLargeFiber36Block0Chunk1Row_13_ok,
    tttLargeFiber36Block0Chunk1Row_14_ok,
    tttLargeFiber36Block0Chunk1Row_15_ok]

def tttLargeFiber36Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber36Block0Chunk1ParentMapCheck 0
    && tttLargeFiber36Block0Chunk1ParentMapCheck 1
    && tttLargeFiber36Block0Chunk1ParentMapCheck 2
    && tttLargeFiber36Block0Chunk1ParentMapCheck 3
    && tttLargeFiber36Block0Chunk1ParentMapCheck 4
    && tttLargeFiber36Block0Chunk1ParentMapCheck 5
    && tttLargeFiber36Block0Chunk1ParentMapCheck 6
    && tttLargeFiber36Block0Chunk1ParentMapCheck 7
    && tttLargeFiber36Block0Chunk1ParentMapCheck 8
    && tttLargeFiber36Block0Chunk1ParentMapCheck 9
    && tttLargeFiber36Block0Chunk1ParentMapCheck 10
    && tttLargeFiber36Block0Chunk1ParentMapCheck 11
    && tttLargeFiber36Block0Chunk1ParentMapCheck 12
    && tttLargeFiber36Block0Chunk1ParentMapCheck 13
    && tttLargeFiber36Block0Chunk1ParentMapCheck 14
    && tttLargeFiber36Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber36Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber36Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber36Block0Chunk1ParentMapAudit,
    tttLargeFiber36Block0Chunk1ParentMap_0_ok,
    tttLargeFiber36Block0Chunk1ParentMap_1_ok,
    tttLargeFiber36Block0Chunk1ParentMap_2_ok,
    tttLargeFiber36Block0Chunk1ParentMap_3_ok,
    tttLargeFiber36Block0Chunk1ParentMap_4_ok,
    tttLargeFiber36Block0Chunk1ParentMap_5_ok,
    tttLargeFiber36Block0Chunk1ParentMap_6_ok,
    tttLargeFiber36Block0Chunk1ParentMap_7_ok,
    tttLargeFiber36Block0Chunk1ParentMap_8_ok,
    tttLargeFiber36Block0Chunk1ParentMap_9_ok,
    tttLargeFiber36Block0Chunk1ParentMap_10_ok,
    tttLargeFiber36Block0Chunk1ParentMap_11_ok,
    tttLargeFiber36Block0Chunk1ParentMap_12_ok,
    tttLargeFiber36Block0Chunk1ParentMap_13_ok,
    tttLargeFiber36Block0Chunk1ParentMap_14_ok,
    tttLargeFiber36Block0Chunk1ParentMap_15_ok]

def tttLargeFiber36Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber36Block0Chunk1ParentPathCheck 0
    && tttLargeFiber36Block0Chunk1ParentPathCheck 1
    && tttLargeFiber36Block0Chunk1ParentPathCheck 2
    && tttLargeFiber36Block0Chunk1ParentPathCheck 3
    && tttLargeFiber36Block0Chunk1ParentPathCheck 4
    && tttLargeFiber36Block0Chunk1ParentPathCheck 5
    && tttLargeFiber36Block0Chunk1ParentPathCheck 6
    && tttLargeFiber36Block0Chunk1ParentPathCheck 7
    && tttLargeFiber36Block0Chunk1ParentPathCheck 8
    && tttLargeFiber36Block0Chunk1ParentPathCheck 9
    && tttLargeFiber36Block0Chunk1ParentPathCheck 10
    && tttLargeFiber36Block0Chunk1ParentPathCheck 11
    && tttLargeFiber36Block0Chunk1ParentPathCheck 12
    && tttLargeFiber36Block0Chunk1ParentPathCheck 13
    && tttLargeFiber36Block0Chunk1ParentPathCheck 14
    && tttLargeFiber36Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber36Block0Chunk1ParentsAudit_ok :
    tttLargeFiber36Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber36Block0Chunk1ParentsAudit,
    tttLargeFiber36Block0Chunk1ParentPath_0_ok,
    tttLargeFiber36Block0Chunk1ParentPath_1_ok,
    tttLargeFiber36Block0Chunk1ParentPath_2_ok,
    tttLargeFiber36Block0Chunk1ParentPath_3_ok,
    tttLargeFiber36Block0Chunk1ParentPath_4_ok,
    tttLargeFiber36Block0Chunk1ParentPath_5_ok,
    tttLargeFiber36Block0Chunk1ParentPath_6_ok,
    tttLargeFiber36Block0Chunk1ParentPath_7_ok,
    tttLargeFiber36Block0Chunk1ParentPath_8_ok,
    tttLargeFiber36Block0Chunk1ParentPath_9_ok,
    tttLargeFiber36Block0Chunk1ParentPath_10_ok,
    tttLargeFiber36Block0Chunk1ParentPath_11_ok,
    tttLargeFiber36Block0Chunk1ParentPath_12_ok,
    tttLargeFiber36Block0Chunk1ParentPath_13_ok,
    tttLargeFiber36Block0Chunk1ParentPath_14_ok,
    tttLargeFiber36Block0Chunk1ParentPath_15_ok]

def tttLargeFiber36Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block0Chunk1SourcesCheck &&
    tttLargeFiber36Block0Chunk1RowsAudit &&
    tttLargeFiber36Block0Chunk1ParentMapAudit &&
    tttLargeFiber36Block0Chunk1ParentsAudit

theorem tttLargeFiber36Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber36Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block0Chunk1SourcesCheck_ok,
    tttLargeFiber36Block0Chunk1RowsAudit_ok,
    tttLargeFiber36Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber36Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
