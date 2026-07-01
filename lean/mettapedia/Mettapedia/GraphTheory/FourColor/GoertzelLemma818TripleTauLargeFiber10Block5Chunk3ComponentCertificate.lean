import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 5 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block5Chunk3Sources : List Nat :=
  [   4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215,
   4216, 4217, 4218, 4219, 4220, 4221, 4222, 4223]

def tttLargeFiber10Row368 : TripleComponentParentRow :=
  tripleRow 4208 4336 125 190 64 127 126 64
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row369 : TripleComponentParentRow :=
  tripleRow 4209 4337 125 190 65 127 126 65
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row370 : TripleComponentParentRow :=
  tripleRow 4210 4338 125 190 66 127 126 66
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row371 : TripleComponentParentRow :=
  tripleRow 4211 4195 125 190 67 125 188 135
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

def tttLargeFiber10Row372 : TripleComponentParentRow :=
  tripleRow 4212 4180 125 190 116 125 142 48
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

def tttLargeFiber10Row373 : TripleComponentParentRow :=
  tripleRow 4213 4181 125 190 117 125 142 49
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

def tttLargeFiber10Row374 : TripleComponentParentRow :=
  tripleRow 4214 4342 125 190 118 127 126 118
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row375 : TripleComponentParentRow :=
  tripleRow 4215 4343 125 190 119 127 126 119
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row376 : TripleComponentParentRow :=
  tripleRow 4216 4344 125 191 72 127 127 72
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row377 : TripleComponentParentRow :=
  tripleRow 4217 4345 125 191 73 127 127 73
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row378 : TripleComponentParentRow :=
  tripleRow 4218 4346 125 191 74 127 127 74
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row379 : TripleComponentParentRow :=
  tripleRow 4219 4347 125 191 75 127 127 75
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row380 : TripleComponentParentRow :=
  tripleRow 4220 4188 125 191 124 125 143 56
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

def tttLargeFiber10Row381 : TripleComponentParentRow :=
  tripleRow 4221 4189 125 191 125 125 143 57
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

def tttLargeFiber10Row382 : TripleComponentParentRow :=
  tripleRow 4222 4350 125 191 126 127 127 126
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Row383 : TripleComponentParentRow :=
  tripleRow 4223 4351 125 191 127 127 127 127
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber10Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row368
  , tttLargeFiber10Row369
  , tttLargeFiber10Row370
  , tttLargeFiber10Row371
  , tttLargeFiber10Row372
  , tttLargeFiber10Row373
  , tttLargeFiber10Row374
  , tttLargeFiber10Row375
  , tttLargeFiber10Row376
  , tttLargeFiber10Row377
  , tttLargeFiber10Row378
  , tttLargeFiber10Row379
  , tttLargeFiber10Row380
  , tttLargeFiber10Row381
  , tttLargeFiber10Row382
  , tttLargeFiber10Row383
  ]

def tttLargeFiber10Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber10Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber10Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber10Block5Chunk3Sources

theorem tttLargeFiber10Block5Chunk3SourcesCheck_ok :
    tttLargeFiber10Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber10Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block5Chunk3RowValid
    (listGetD tttLargeFiber10Block5Chunk3Rows i default)

def tttLargeFiber10Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block5Chunk3Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block5Chunk3Sources 0 0 == 4208
      && tttLargeFiber10ParentOf 4208 == 4336
      && tttLargeFiber10ParentOf 4336 == 2496
      && tttLargeFiber10ParentOf 2496 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block5Chunk3Sources 1 0 == 4209
      && tttLargeFiber10ParentOf 4209 == 4337
      && tttLargeFiber10ParentOf 4337 == 2497
      && tttLargeFiber10ParentOf 2497 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block5Chunk3Sources 2 0 == 4210
      && tttLargeFiber10ParentOf 4210 == 4338
      && tttLargeFiber10ParentOf 4338 == 2498
      && tttLargeFiber10ParentOf 2498 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block5Chunk3Sources 3 0 == 4211
      && tttLargeFiber10ParentOf 4211 == 4195
      && tttLargeFiber10ParentOf 4195 == 4163
      && tttLargeFiber10ParentOf 4163 == 4160
      && tttLargeFiber10ParentOf 4160 == 4288
      && tttLargeFiber10ParentOf 4288 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block5Chunk3Sources 4 0 == 4212
      && tttLargeFiber10ParentOf 4212 == 4180
      && tttLargeFiber10ParentOf 4180 == 4168
      && tttLargeFiber10ParentOf 4168 == 4296
      && tttLargeFiber10ParentOf 4296 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block5Chunk3Sources 5 0 == 4213
      && tttLargeFiber10ParentOf 4213 == 4181
      && tttLargeFiber10ParentOf 4181 == 4169
      && tttLargeFiber10ParentOf 4169 == 4297
      && tttLargeFiber10ParentOf 4297 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block5Chunk3Sources 6 0 == 4214
      && tttLargeFiber10ParentOf 4214 == 4342
      && tttLargeFiber10ParentOf 4342 == 2502
      && tttLargeFiber10ParentOf 2502 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (6 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block5Chunk3Sources 7 0 == 4215
      && tttLargeFiber10ParentOf 4215 == 4343
      && tttLargeFiber10ParentOf 4343 == 2503
      && tttLargeFiber10ParentOf 2503 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block5Chunk3Sources 8 0 == 4216
      && tttLargeFiber10ParentOf 4216 == 4344
      && tttLargeFiber10ParentOf 4344 == 2504
      && tttLargeFiber10ParentOf 2504 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block5Chunk3Sources 9 0 == 4217
      && tttLargeFiber10ParentOf 4217 == 4345
      && tttLargeFiber10ParentOf 4345 == 2505
      && tttLargeFiber10ParentOf 2505 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block5Chunk3Sources 10 0 == 4218
      && tttLargeFiber10ParentOf 4218 == 4346
      && tttLargeFiber10ParentOf 4346 == 2506
      && tttLargeFiber10ParentOf 2506 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block5Chunk3Sources 11 0 == 4219
      && tttLargeFiber10ParentOf 4219 == 4347
      && tttLargeFiber10ParentOf 4347 == 2507
      && tttLargeFiber10ParentOf 2507 == 2451
      && tttLargeFiber10ParentOf 2451 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block5Chunk3Sources 12 0 == 4220
      && tttLargeFiber10ParentOf 4220 == 4188
      && tttLargeFiber10ParentOf 4188 == 4160
      && tttLargeFiber10ParentOf 4160 == 4288
      && tttLargeFiber10ParentOf 4288 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block5Chunk3Sources 13 0 == 4221
      && tttLargeFiber10ParentOf 4221 == 4189
      && tttLargeFiber10ParentOf 4189 == 4161
      && tttLargeFiber10ParentOf 4161 == 4289
      && tttLargeFiber10ParentOf 4289 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block5Chunk3Sources 14 0 == 4222
      && tttLargeFiber10ParentOf 4222 == 4350
      && tttLargeFiber10ParentOf 4350 == 2510
      && tttLargeFiber10ParentOf 2510 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block5Chunk3Sources 15 0 == 4223
      && tttLargeFiber10ParentOf 4223 == 4351
      && tttLargeFiber10ParentOf 4351 == 2511
      && tttLargeFiber10ParentOf 2511 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block5Chunk3Row_0_ok :
    tttLargeFiber10Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_1_ok :
    tttLargeFiber10Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_2_ok :
    tttLargeFiber10Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_3_ok :
    tttLargeFiber10Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_4_ok :
    tttLargeFiber10Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_5_ok :
    tttLargeFiber10Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_6_ok :
    tttLargeFiber10Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_7_ok :
    tttLargeFiber10Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_8_ok :
    tttLargeFiber10Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_9_ok :
    tttLargeFiber10Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_10_ok :
    tttLargeFiber10Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_11_ok :
    tttLargeFiber10Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_12_ok :
    tttLargeFiber10Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_13_ok :
    tttLargeFiber10Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_14_ok :
    tttLargeFiber10Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3Row_15_ok :
    tttLargeFiber10Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_0_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_1_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_2_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_3_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_4_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_5_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_6_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_7_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_8_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_9_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_10_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_11_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_12_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_13_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_14_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentMap_15_ok :
    tttLargeFiber10Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_0_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_1_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_2_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_3_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_4_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_5_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_6_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_7_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_8_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_9_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_10_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_11_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_12_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_13_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_14_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block5Chunk3ParentPath_15_ok :
    tttLargeFiber10Block5Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber10Block5Chunk3RowCheck 0
    && tttLargeFiber10Block5Chunk3RowCheck 1
    && tttLargeFiber10Block5Chunk3RowCheck 2
    && tttLargeFiber10Block5Chunk3RowCheck 3
    && tttLargeFiber10Block5Chunk3RowCheck 4
    && tttLargeFiber10Block5Chunk3RowCheck 5
    && tttLargeFiber10Block5Chunk3RowCheck 6
    && tttLargeFiber10Block5Chunk3RowCheck 7
    && tttLargeFiber10Block5Chunk3RowCheck 8
    && tttLargeFiber10Block5Chunk3RowCheck 9
    && tttLargeFiber10Block5Chunk3RowCheck 10
    && tttLargeFiber10Block5Chunk3RowCheck 11
    && tttLargeFiber10Block5Chunk3RowCheck 12
    && tttLargeFiber10Block5Chunk3RowCheck 13
    && tttLargeFiber10Block5Chunk3RowCheck 14
    && tttLargeFiber10Block5Chunk3RowCheck 15

theorem tttLargeFiber10Block5Chunk3RowsAudit_ok :
    tttLargeFiber10Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber10Block5Chunk3RowsAudit,
    tttLargeFiber10Block5Chunk3Row_0_ok,
    tttLargeFiber10Block5Chunk3Row_1_ok,
    tttLargeFiber10Block5Chunk3Row_2_ok,
    tttLargeFiber10Block5Chunk3Row_3_ok,
    tttLargeFiber10Block5Chunk3Row_4_ok,
    tttLargeFiber10Block5Chunk3Row_5_ok,
    tttLargeFiber10Block5Chunk3Row_6_ok,
    tttLargeFiber10Block5Chunk3Row_7_ok,
    tttLargeFiber10Block5Chunk3Row_8_ok,
    tttLargeFiber10Block5Chunk3Row_9_ok,
    tttLargeFiber10Block5Chunk3Row_10_ok,
    tttLargeFiber10Block5Chunk3Row_11_ok,
    tttLargeFiber10Block5Chunk3Row_12_ok,
    tttLargeFiber10Block5Chunk3Row_13_ok,
    tttLargeFiber10Block5Chunk3Row_14_ok,
    tttLargeFiber10Block5Chunk3Row_15_ok]

def tttLargeFiber10Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber10Block5Chunk3ParentMapCheck 0
    && tttLargeFiber10Block5Chunk3ParentMapCheck 1
    && tttLargeFiber10Block5Chunk3ParentMapCheck 2
    && tttLargeFiber10Block5Chunk3ParentMapCheck 3
    && tttLargeFiber10Block5Chunk3ParentMapCheck 4
    && tttLargeFiber10Block5Chunk3ParentMapCheck 5
    && tttLargeFiber10Block5Chunk3ParentMapCheck 6
    && tttLargeFiber10Block5Chunk3ParentMapCheck 7
    && tttLargeFiber10Block5Chunk3ParentMapCheck 8
    && tttLargeFiber10Block5Chunk3ParentMapCheck 9
    && tttLargeFiber10Block5Chunk3ParentMapCheck 10
    && tttLargeFiber10Block5Chunk3ParentMapCheck 11
    && tttLargeFiber10Block5Chunk3ParentMapCheck 12
    && tttLargeFiber10Block5Chunk3ParentMapCheck 13
    && tttLargeFiber10Block5Chunk3ParentMapCheck 14
    && tttLargeFiber10Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber10Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber10Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber10Block5Chunk3ParentMapAudit,
    tttLargeFiber10Block5Chunk3ParentMap_0_ok,
    tttLargeFiber10Block5Chunk3ParentMap_1_ok,
    tttLargeFiber10Block5Chunk3ParentMap_2_ok,
    tttLargeFiber10Block5Chunk3ParentMap_3_ok,
    tttLargeFiber10Block5Chunk3ParentMap_4_ok,
    tttLargeFiber10Block5Chunk3ParentMap_5_ok,
    tttLargeFiber10Block5Chunk3ParentMap_6_ok,
    tttLargeFiber10Block5Chunk3ParentMap_7_ok,
    tttLargeFiber10Block5Chunk3ParentMap_8_ok,
    tttLargeFiber10Block5Chunk3ParentMap_9_ok,
    tttLargeFiber10Block5Chunk3ParentMap_10_ok,
    tttLargeFiber10Block5Chunk3ParentMap_11_ok,
    tttLargeFiber10Block5Chunk3ParentMap_12_ok,
    tttLargeFiber10Block5Chunk3ParentMap_13_ok,
    tttLargeFiber10Block5Chunk3ParentMap_14_ok,
    tttLargeFiber10Block5Chunk3ParentMap_15_ok]

def tttLargeFiber10Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber10Block5Chunk3ParentPathCheck 0
    && tttLargeFiber10Block5Chunk3ParentPathCheck 1
    && tttLargeFiber10Block5Chunk3ParentPathCheck 2
    && tttLargeFiber10Block5Chunk3ParentPathCheck 3
    && tttLargeFiber10Block5Chunk3ParentPathCheck 4
    && tttLargeFiber10Block5Chunk3ParentPathCheck 5
    && tttLargeFiber10Block5Chunk3ParentPathCheck 6
    && tttLargeFiber10Block5Chunk3ParentPathCheck 7
    && tttLargeFiber10Block5Chunk3ParentPathCheck 8
    && tttLargeFiber10Block5Chunk3ParentPathCheck 9
    && tttLargeFiber10Block5Chunk3ParentPathCheck 10
    && tttLargeFiber10Block5Chunk3ParentPathCheck 11
    && tttLargeFiber10Block5Chunk3ParentPathCheck 12
    && tttLargeFiber10Block5Chunk3ParentPathCheck 13
    && tttLargeFiber10Block5Chunk3ParentPathCheck 14
    && tttLargeFiber10Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber10Block5Chunk3ParentsAudit_ok :
    tttLargeFiber10Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber10Block5Chunk3ParentsAudit,
    tttLargeFiber10Block5Chunk3ParentPath_0_ok,
    tttLargeFiber10Block5Chunk3ParentPath_1_ok,
    tttLargeFiber10Block5Chunk3ParentPath_2_ok,
    tttLargeFiber10Block5Chunk3ParentPath_3_ok,
    tttLargeFiber10Block5Chunk3ParentPath_4_ok,
    tttLargeFiber10Block5Chunk3ParentPath_5_ok,
    tttLargeFiber10Block5Chunk3ParentPath_6_ok,
    tttLargeFiber10Block5Chunk3ParentPath_7_ok,
    tttLargeFiber10Block5Chunk3ParentPath_8_ok,
    tttLargeFiber10Block5Chunk3ParentPath_9_ok,
    tttLargeFiber10Block5Chunk3ParentPath_10_ok,
    tttLargeFiber10Block5Chunk3ParentPath_11_ok,
    tttLargeFiber10Block5Chunk3ParentPath_12_ok,
    tttLargeFiber10Block5Chunk3ParentPath_13_ok,
    tttLargeFiber10Block5Chunk3ParentPath_14_ok,
    tttLargeFiber10Block5Chunk3ParentPath_15_ok]

def tttLargeFiber10Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block5Chunk3SourcesCheck &&
    tttLargeFiber10Block5Chunk3RowsAudit &&
    tttLargeFiber10Block5Chunk3ParentMapAudit &&
    tttLargeFiber10Block5Chunk3ParentsAudit

theorem tttLargeFiber10Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber10Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block5Chunk3SourcesCheck_ok,
    tttLargeFiber10Block5Chunk3RowsAudit_ok,
    tttLargeFiber10Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber10Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
