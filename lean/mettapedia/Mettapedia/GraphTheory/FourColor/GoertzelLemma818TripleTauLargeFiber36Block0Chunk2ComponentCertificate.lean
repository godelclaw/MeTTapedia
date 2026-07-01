import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 0 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block0Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block0Chunk2Sources : List Nat :=
  [   304, 305, 306, 307, 308, 309, 310, 311,
   312, 313, 314, 315, 316, 317, 318, 319]

def tttLargeFiber36Row32 : TripleComponentParentRow :=
  tripleRow 304 320 8 100 132 8 102 64
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row33 : TripleComponentParentRow :=
  tripleRow 305 321 8 100 133 8 102 65
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row34 : TripleComponentParentRow :=
  tripleRow 306 294 8 100 134 8 82 34
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row35 : TripleComponentParentRow :=
  tripleRow 307 295 8 100 135 8 82 35
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row36 : TripleComponentParentRow :=
  tripleRow 308 290 8 100 180 8 82 18
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row37 : TripleComponentParentRow :=
  tripleRow 309 311 8 100 181 8 100 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row38 : TripleComponentParentRow :=
  tripleRow 310 289 8 100 182 8 82 17
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber36Row39 : TripleComponentParentRow :=
  tripleRow 311 288 8 100 183 8 82 16
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber36Row40 : TripleComponentParentRow :=
  tripleRow 312 328 8 101 140 8 103 72
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row41 : TripleComponentParentRow :=
  tripleRow 313 329 8 101 141 8 103 73
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row42 : TripleComponentParentRow :=
  tripleRow 314 330 8 101 142 8 103 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row43 : TripleComponentParentRow :=
  tripleRow 315 312 8 101 143 8 101 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row44 : TripleComponentParentRow :=
  tripleRow 316 312 8 101 188 8 101 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row45 : TripleComponentParentRow :=
  tripleRow 317 313 8 101 189 8 101 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row46 : TripleComponentParentRow :=
  tripleRow 318 334 8 101 190 8 103 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row47 : TripleComponentParentRow :=
  tripleRow 319 335 8 101 191 8 103 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Block0Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row32
  , tttLargeFiber36Row33
  , tttLargeFiber36Row34
  , tttLargeFiber36Row35
  , tttLargeFiber36Row36
  , tttLargeFiber36Row37
  , tttLargeFiber36Row38
  , tttLargeFiber36Row39
  , tttLargeFiber36Row40
  , tttLargeFiber36Row41
  , tttLargeFiber36Row42
  , tttLargeFiber36Row43
  , tttLargeFiber36Row44
  , tttLargeFiber36Row45
  , tttLargeFiber36Row46
  , tttLargeFiber36Row47
  ]

def tttLargeFiber36Block0Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block0Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block0Chunk2ExpectedContains row.source &&
    tttLargeFiber36Block0Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block0Chunk2SourcesCheck : Bool :=
  (tttLargeFiber36Block0Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber36Block0Chunk2Sources

theorem tttLargeFiber36Block0Chunk2SourcesCheck_ok :
    tttLargeFiber36Block0Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber36Block0Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block0Chunk2RowValid
    (listGetD tttLargeFiber36Block0Chunk2Rows i default)

def tttLargeFiber36Block0Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block0Chunk2Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block0Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block0Chunk2Sources 0 0 == 304
      && tttLargeFiber36ParentOf 304 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block0Chunk2Sources 1 0 == 305
      && tttLargeFiber36ParentOf 305 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block0Chunk2Sources 2 0 == 306
      && tttLargeFiber36ParentOf 306 == 294
      && tttLargeFiber36ParentOf 294 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block0Chunk2Sources 3 0 == 307
      && tttLargeFiber36ParentOf 307 == 295
      && tttLargeFiber36ParentOf 295 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block0Chunk2Sources 4 0 == 308
      && tttLargeFiber36ParentOf 308 == 290
      && tttLargeFiber36ParentOf 290 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block0Chunk2Sources 5 0 == 309
      && tttLargeFiber36ParentOf 309 == 311
      && tttLargeFiber36ParentOf 311 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block0Chunk2Sources 6 0 == 310
      && tttLargeFiber36ParentOf 310 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block0Chunk2Sources 7 0 == 311
      && tttLargeFiber36ParentOf 311 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block0Chunk2Sources 8 0 == 312
      && tttLargeFiber36ParentOf 312 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block0Chunk2Sources 9 0 == 313
      && tttLargeFiber36ParentOf 313 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block0Chunk2Sources 10 0 == 314
      && tttLargeFiber36ParentOf 314 == 330
      && tttLargeFiber36ParentOf 330 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block0Chunk2Sources 11 0 == 315
      && tttLargeFiber36ParentOf 315 == 312
      && tttLargeFiber36ParentOf 312 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block0Chunk2Sources 12 0 == 316
      && tttLargeFiber36ParentOf 316 == 312
      && tttLargeFiber36ParentOf 312 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block0Chunk2Sources 13 0 == 317
      && tttLargeFiber36ParentOf 317 == 313
      && tttLargeFiber36ParentOf 313 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block0Chunk2Sources 14 0 == 318
      && tttLargeFiber36ParentOf 318 == 334
      && tttLargeFiber36ParentOf 334 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block0Chunk2Sources 15 0 == 319
      && tttLargeFiber36ParentOf 319 == 335
      && tttLargeFiber36ParentOf 335 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block0Chunk2Row_0_ok :
    tttLargeFiber36Block0Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_1_ok :
    tttLargeFiber36Block0Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_2_ok :
    tttLargeFiber36Block0Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_3_ok :
    tttLargeFiber36Block0Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_4_ok :
    tttLargeFiber36Block0Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_5_ok :
    tttLargeFiber36Block0Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_6_ok :
    tttLargeFiber36Block0Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_7_ok :
    tttLargeFiber36Block0Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_8_ok :
    tttLargeFiber36Block0Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_9_ok :
    tttLargeFiber36Block0Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_10_ok :
    tttLargeFiber36Block0Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_11_ok :
    tttLargeFiber36Block0Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_12_ok :
    tttLargeFiber36Block0Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_13_ok :
    tttLargeFiber36Block0Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_14_ok :
    tttLargeFiber36Block0Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2Row_15_ok :
    tttLargeFiber36Block0Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_0_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_1_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_2_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_3_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_4_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_5_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_6_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_7_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_8_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_9_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_10_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_11_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_12_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_13_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_14_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentMap_15_ok :
    tttLargeFiber36Block0Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_0_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_1_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_2_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_3_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_4_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_5_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_6_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_7_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_8_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_9_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_10_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_11_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_12_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_13_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_14_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk2ParentPath_15_ok :
    tttLargeFiber36Block0Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block0Chunk2RowsAudit : Bool :=
  tttLargeFiber36Block0Chunk2RowCheck 0
    && tttLargeFiber36Block0Chunk2RowCheck 1
    && tttLargeFiber36Block0Chunk2RowCheck 2
    && tttLargeFiber36Block0Chunk2RowCheck 3
    && tttLargeFiber36Block0Chunk2RowCheck 4
    && tttLargeFiber36Block0Chunk2RowCheck 5
    && tttLargeFiber36Block0Chunk2RowCheck 6
    && tttLargeFiber36Block0Chunk2RowCheck 7
    && tttLargeFiber36Block0Chunk2RowCheck 8
    && tttLargeFiber36Block0Chunk2RowCheck 9
    && tttLargeFiber36Block0Chunk2RowCheck 10
    && tttLargeFiber36Block0Chunk2RowCheck 11
    && tttLargeFiber36Block0Chunk2RowCheck 12
    && tttLargeFiber36Block0Chunk2RowCheck 13
    && tttLargeFiber36Block0Chunk2RowCheck 14
    && tttLargeFiber36Block0Chunk2RowCheck 15

theorem tttLargeFiber36Block0Chunk2RowsAudit_ok :
    tttLargeFiber36Block0Chunk2RowsAudit = true := by
  simp [tttLargeFiber36Block0Chunk2RowsAudit,
    tttLargeFiber36Block0Chunk2Row_0_ok,
    tttLargeFiber36Block0Chunk2Row_1_ok,
    tttLargeFiber36Block0Chunk2Row_2_ok,
    tttLargeFiber36Block0Chunk2Row_3_ok,
    tttLargeFiber36Block0Chunk2Row_4_ok,
    tttLargeFiber36Block0Chunk2Row_5_ok,
    tttLargeFiber36Block0Chunk2Row_6_ok,
    tttLargeFiber36Block0Chunk2Row_7_ok,
    tttLargeFiber36Block0Chunk2Row_8_ok,
    tttLargeFiber36Block0Chunk2Row_9_ok,
    tttLargeFiber36Block0Chunk2Row_10_ok,
    tttLargeFiber36Block0Chunk2Row_11_ok,
    tttLargeFiber36Block0Chunk2Row_12_ok,
    tttLargeFiber36Block0Chunk2Row_13_ok,
    tttLargeFiber36Block0Chunk2Row_14_ok,
    tttLargeFiber36Block0Chunk2Row_15_ok]

def tttLargeFiber36Block0Chunk2ParentMapAudit : Bool :=
  tttLargeFiber36Block0Chunk2ParentMapCheck 0
    && tttLargeFiber36Block0Chunk2ParentMapCheck 1
    && tttLargeFiber36Block0Chunk2ParentMapCheck 2
    && tttLargeFiber36Block0Chunk2ParentMapCheck 3
    && tttLargeFiber36Block0Chunk2ParentMapCheck 4
    && tttLargeFiber36Block0Chunk2ParentMapCheck 5
    && tttLargeFiber36Block0Chunk2ParentMapCheck 6
    && tttLargeFiber36Block0Chunk2ParentMapCheck 7
    && tttLargeFiber36Block0Chunk2ParentMapCheck 8
    && tttLargeFiber36Block0Chunk2ParentMapCheck 9
    && tttLargeFiber36Block0Chunk2ParentMapCheck 10
    && tttLargeFiber36Block0Chunk2ParentMapCheck 11
    && tttLargeFiber36Block0Chunk2ParentMapCheck 12
    && tttLargeFiber36Block0Chunk2ParentMapCheck 13
    && tttLargeFiber36Block0Chunk2ParentMapCheck 14
    && tttLargeFiber36Block0Chunk2ParentMapCheck 15

theorem tttLargeFiber36Block0Chunk2ParentMapAudit_ok :
    tttLargeFiber36Block0Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber36Block0Chunk2ParentMapAudit,
    tttLargeFiber36Block0Chunk2ParentMap_0_ok,
    tttLargeFiber36Block0Chunk2ParentMap_1_ok,
    tttLargeFiber36Block0Chunk2ParentMap_2_ok,
    tttLargeFiber36Block0Chunk2ParentMap_3_ok,
    tttLargeFiber36Block0Chunk2ParentMap_4_ok,
    tttLargeFiber36Block0Chunk2ParentMap_5_ok,
    tttLargeFiber36Block0Chunk2ParentMap_6_ok,
    tttLargeFiber36Block0Chunk2ParentMap_7_ok,
    tttLargeFiber36Block0Chunk2ParentMap_8_ok,
    tttLargeFiber36Block0Chunk2ParentMap_9_ok,
    tttLargeFiber36Block0Chunk2ParentMap_10_ok,
    tttLargeFiber36Block0Chunk2ParentMap_11_ok,
    tttLargeFiber36Block0Chunk2ParentMap_12_ok,
    tttLargeFiber36Block0Chunk2ParentMap_13_ok,
    tttLargeFiber36Block0Chunk2ParentMap_14_ok,
    tttLargeFiber36Block0Chunk2ParentMap_15_ok]

def tttLargeFiber36Block0Chunk2ParentsAudit : Bool :=
  tttLargeFiber36Block0Chunk2ParentPathCheck 0
    && tttLargeFiber36Block0Chunk2ParentPathCheck 1
    && tttLargeFiber36Block0Chunk2ParentPathCheck 2
    && tttLargeFiber36Block0Chunk2ParentPathCheck 3
    && tttLargeFiber36Block0Chunk2ParentPathCheck 4
    && tttLargeFiber36Block0Chunk2ParentPathCheck 5
    && tttLargeFiber36Block0Chunk2ParentPathCheck 6
    && tttLargeFiber36Block0Chunk2ParentPathCheck 7
    && tttLargeFiber36Block0Chunk2ParentPathCheck 8
    && tttLargeFiber36Block0Chunk2ParentPathCheck 9
    && tttLargeFiber36Block0Chunk2ParentPathCheck 10
    && tttLargeFiber36Block0Chunk2ParentPathCheck 11
    && tttLargeFiber36Block0Chunk2ParentPathCheck 12
    && tttLargeFiber36Block0Chunk2ParentPathCheck 13
    && tttLargeFiber36Block0Chunk2ParentPathCheck 14
    && tttLargeFiber36Block0Chunk2ParentPathCheck 15

theorem tttLargeFiber36Block0Chunk2ParentsAudit_ok :
    tttLargeFiber36Block0Chunk2ParentsAudit = true := by
  simp [tttLargeFiber36Block0Chunk2ParentsAudit,
    tttLargeFiber36Block0Chunk2ParentPath_0_ok,
    tttLargeFiber36Block0Chunk2ParentPath_1_ok,
    tttLargeFiber36Block0Chunk2ParentPath_2_ok,
    tttLargeFiber36Block0Chunk2ParentPath_3_ok,
    tttLargeFiber36Block0Chunk2ParentPath_4_ok,
    tttLargeFiber36Block0Chunk2ParentPath_5_ok,
    tttLargeFiber36Block0Chunk2ParentPath_6_ok,
    tttLargeFiber36Block0Chunk2ParentPath_7_ok,
    tttLargeFiber36Block0Chunk2ParentPath_8_ok,
    tttLargeFiber36Block0Chunk2ParentPath_9_ok,
    tttLargeFiber36Block0Chunk2ParentPath_10_ok,
    tttLargeFiber36Block0Chunk2ParentPath_11_ok,
    tttLargeFiber36Block0Chunk2ParentPath_12_ok,
    tttLargeFiber36Block0Chunk2ParentPath_13_ok,
    tttLargeFiber36Block0Chunk2ParentPath_14_ok,
    tttLargeFiber36Block0Chunk2ParentPath_15_ok]

def tttLargeFiber36Block0Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block0Chunk2SourcesCheck &&
    tttLargeFiber36Block0Chunk2RowsAudit &&
    tttLargeFiber36Block0Chunk2ParentMapAudit &&
    tttLargeFiber36Block0Chunk2ParentsAudit

theorem tttLargeFiber36Block0Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber36Block0Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block0Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block0Chunk2SourcesCheck_ok,
    tttLargeFiber36Block0Chunk2RowsAudit_ok,
    tttLargeFiber36Block0Chunk2ParentMapAudit_ok,
    tttLargeFiber36Block0Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block0Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
