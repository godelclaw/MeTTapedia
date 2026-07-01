import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 5 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block5Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block5Chunk0Sources : List Nat :=
  [   4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167,
   4168, 4169, 4170, 4171, 4172, 4173, 4174, 4175]

def tttLargeFiber10Row320 : TripleComponentParentRow :=
  tripleRow 4160 4288 125 140 148 127 72 80
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row321 : TripleComponentParentRow :=
  tripleRow 4161 4289 125 140 149 127 72 81
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row322 : TripleComponentParentRow :=
  tripleRow 4162 4290 125 140 150 127 72 82
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row323 : TripleComponentParentRow :=
  tripleRow 4163 4160 125 140 151 125 140 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row324 : TripleComponentParentRow :=
  tripleRow 4164 4160 125 140 164 125 140 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row325 : TripleComponentParentRow :=
  tripleRow 4165 4161 125 140 165 125 140 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row326 : TripleComponentParentRow :=
  tripleRow 4166 4294 125 140 166 127 72 102
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row327 : TripleComponentParentRow :=
  tripleRow 4167 4295 125 140 167 127 72 103
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row328 : TripleComponentParentRow :=
  tripleRow 4168 4296 125 141 156 127 73 88
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row329 : TripleComponentParentRow :=
  tripleRow 4169 4297 125 141 157 127 73 89
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row330 : TripleComponentParentRow :=
  tripleRow 4170 4298 125 141 158 127 73 90
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber10Row331 : TripleComponentParentRow :=
  tripleRow 4171 4168 125 141 159 125 141 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row332 : TripleComponentParentRow :=
  tripleRow 4172 4168 125 141 172 125 141 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row333 : TripleComponentParentRow :=
  tripleRow 4173 4169 125 141 173 125 141 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row334 : TripleComponentParentRow :=
  tripleRow 4174 4302 125 141 174 127 73 110
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Row335 : TripleComponentParentRow :=
  tripleRow 4175 4303 125 141 175 127 73 111
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber10Block5Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row320
  , tttLargeFiber10Row321
  , tttLargeFiber10Row322
  , tttLargeFiber10Row323
  , tttLargeFiber10Row324
  , tttLargeFiber10Row325
  , tttLargeFiber10Row326
  , tttLargeFiber10Row327
  , tttLargeFiber10Row328
  , tttLargeFiber10Row329
  , tttLargeFiber10Row330
  , tttLargeFiber10Row331
  , tttLargeFiber10Row332
  , tttLargeFiber10Row333
  , tttLargeFiber10Row334
  , tttLargeFiber10Row335
  ]

def tttLargeFiber10Block5Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block5Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block5Chunk0ExpectedContains row.source &&
    tttLargeFiber10Block5Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block5Chunk0SourcesCheck : Bool :=
  (tttLargeFiber10Block5Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber10Block5Chunk0Sources

theorem tttLargeFiber10Block5Chunk0SourcesCheck_ok :
    tttLargeFiber10Block5Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber10Block5Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block5Chunk0RowValid
    (listGetD tttLargeFiber10Block5Chunk0Rows i default)

def tttLargeFiber10Block5Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block5Chunk0Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block5Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block5Chunk0Sources 0 0 == 4160
      && tttLargeFiber10ParentOf 4160 == 4288
      && tttLargeFiber10ParentOf 4288 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (2 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block5Chunk0Sources 1 0 == 4161
      && tttLargeFiber10ParentOf 4161 == 4289
      && tttLargeFiber10ParentOf 4289 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block5Chunk0Sources 2 0 == 4162
      && tttLargeFiber10ParentOf 4162 == 4290
      && tttLargeFiber10ParentOf 4290 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block5Chunk0Sources 3 0 == 4163
      && tttLargeFiber10ParentOf 4163 == 4160
      && tttLargeFiber10ParentOf 4160 == 4288
      && tttLargeFiber10ParentOf 4288 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block5Chunk0Sources 4 0 == 4164
      && tttLargeFiber10ParentOf 4164 == 4160
      && tttLargeFiber10ParentOf 4160 == 4288
      && tttLargeFiber10ParentOf 4288 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block5Chunk0Sources 5 0 == 4165
      && tttLargeFiber10ParentOf 4165 == 4161
      && tttLargeFiber10ParentOf 4161 == 4289
      && tttLargeFiber10ParentOf 4289 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block5Chunk0Sources 6 0 == 4166
      && tttLargeFiber10ParentOf 4166 == 4294
      && tttLargeFiber10ParentOf 4294 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block5Chunk0Sources 7 0 == 4167
      && tttLargeFiber10ParentOf 4167 == 4295
      && tttLargeFiber10ParentOf 4295 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block5Chunk0Sources 8 0 == 4168
      && tttLargeFiber10ParentOf 4168 == 4296
      && tttLargeFiber10ParentOf 4296 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block5Chunk0Sources 9 0 == 4169
      && tttLargeFiber10ParentOf 4169 == 4297
      && tttLargeFiber10ParentOf 4297 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block5Chunk0Sources 10 0 == 4170
      && tttLargeFiber10ParentOf 4170 == 4298
      && tttLargeFiber10ParentOf 4298 == 2458
      && tttLargeFiber10ParentOf 2458 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block5Chunk0Sources 11 0 == 4171
      && tttLargeFiber10ParentOf 4171 == 4168
      && tttLargeFiber10ParentOf 4168 == 4296
      && tttLargeFiber10ParentOf 4296 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block5Chunk0Sources 12 0 == 4172
      && tttLargeFiber10ParentOf 4172 == 4168
      && tttLargeFiber10ParentOf 4168 == 4296
      && tttLargeFiber10ParentOf 4296 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block5Chunk0Sources 13 0 == 4173
      && tttLargeFiber10ParentOf 4173 == 4169
      && tttLargeFiber10ParentOf 4169 == 4297
      && tttLargeFiber10ParentOf 4297 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block5Chunk0Sources 14 0 == 4174
      && tttLargeFiber10ParentOf 4174 == 4302
      && tttLargeFiber10ParentOf 4302 == 2462
      && tttLargeFiber10ParentOf 2462 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block5Chunk0Sources 15 0 == 4175
      && tttLargeFiber10ParentOf 4175 == 4303
      && tttLargeFiber10ParentOf 4303 == 2463
      && tttLargeFiber10ParentOf 2463 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block5Chunk0Row_0_ok :
    tttLargeFiber10Block5Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_1_ok :
    tttLargeFiber10Block5Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_2_ok :
    tttLargeFiber10Block5Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_3_ok :
    tttLargeFiber10Block5Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_4_ok :
    tttLargeFiber10Block5Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_5_ok :
    tttLargeFiber10Block5Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_6_ok :
    tttLargeFiber10Block5Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_7_ok :
    tttLargeFiber10Block5Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_8_ok :
    tttLargeFiber10Block5Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_9_ok :
    tttLargeFiber10Block5Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_10_ok :
    tttLargeFiber10Block5Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_11_ok :
    tttLargeFiber10Block5Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_12_ok :
    tttLargeFiber10Block5Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_13_ok :
    tttLargeFiber10Block5Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_14_ok :
    tttLargeFiber10Block5Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0Row_15_ok :
    tttLargeFiber10Block5Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_0_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_1_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_2_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_3_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_4_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_5_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_6_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_7_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_8_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_9_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_10_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_11_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_12_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_13_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_14_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentMap_15_ok :
    tttLargeFiber10Block5Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_0_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_1_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_2_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_3_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_4_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_5_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_6_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_7_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_8_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_9_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_10_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_11_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_12_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_13_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_14_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block5Chunk0ParentPath_15_ok :
    tttLargeFiber10Block5Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block5Chunk0RowsAudit : Bool :=
  tttLargeFiber10Block5Chunk0RowCheck 0
    && tttLargeFiber10Block5Chunk0RowCheck 1
    && tttLargeFiber10Block5Chunk0RowCheck 2
    && tttLargeFiber10Block5Chunk0RowCheck 3
    && tttLargeFiber10Block5Chunk0RowCheck 4
    && tttLargeFiber10Block5Chunk0RowCheck 5
    && tttLargeFiber10Block5Chunk0RowCheck 6
    && tttLargeFiber10Block5Chunk0RowCheck 7
    && tttLargeFiber10Block5Chunk0RowCheck 8
    && tttLargeFiber10Block5Chunk0RowCheck 9
    && tttLargeFiber10Block5Chunk0RowCheck 10
    && tttLargeFiber10Block5Chunk0RowCheck 11
    && tttLargeFiber10Block5Chunk0RowCheck 12
    && tttLargeFiber10Block5Chunk0RowCheck 13
    && tttLargeFiber10Block5Chunk0RowCheck 14
    && tttLargeFiber10Block5Chunk0RowCheck 15

theorem tttLargeFiber10Block5Chunk0RowsAudit_ok :
    tttLargeFiber10Block5Chunk0RowsAudit = true := by
  simp [tttLargeFiber10Block5Chunk0RowsAudit,
    tttLargeFiber10Block5Chunk0Row_0_ok,
    tttLargeFiber10Block5Chunk0Row_1_ok,
    tttLargeFiber10Block5Chunk0Row_2_ok,
    tttLargeFiber10Block5Chunk0Row_3_ok,
    tttLargeFiber10Block5Chunk0Row_4_ok,
    tttLargeFiber10Block5Chunk0Row_5_ok,
    tttLargeFiber10Block5Chunk0Row_6_ok,
    tttLargeFiber10Block5Chunk0Row_7_ok,
    tttLargeFiber10Block5Chunk0Row_8_ok,
    tttLargeFiber10Block5Chunk0Row_9_ok,
    tttLargeFiber10Block5Chunk0Row_10_ok,
    tttLargeFiber10Block5Chunk0Row_11_ok,
    tttLargeFiber10Block5Chunk0Row_12_ok,
    tttLargeFiber10Block5Chunk0Row_13_ok,
    tttLargeFiber10Block5Chunk0Row_14_ok,
    tttLargeFiber10Block5Chunk0Row_15_ok]

def tttLargeFiber10Block5Chunk0ParentMapAudit : Bool :=
  tttLargeFiber10Block5Chunk0ParentMapCheck 0
    && tttLargeFiber10Block5Chunk0ParentMapCheck 1
    && tttLargeFiber10Block5Chunk0ParentMapCheck 2
    && tttLargeFiber10Block5Chunk0ParentMapCheck 3
    && tttLargeFiber10Block5Chunk0ParentMapCheck 4
    && tttLargeFiber10Block5Chunk0ParentMapCheck 5
    && tttLargeFiber10Block5Chunk0ParentMapCheck 6
    && tttLargeFiber10Block5Chunk0ParentMapCheck 7
    && tttLargeFiber10Block5Chunk0ParentMapCheck 8
    && tttLargeFiber10Block5Chunk0ParentMapCheck 9
    && tttLargeFiber10Block5Chunk0ParentMapCheck 10
    && tttLargeFiber10Block5Chunk0ParentMapCheck 11
    && tttLargeFiber10Block5Chunk0ParentMapCheck 12
    && tttLargeFiber10Block5Chunk0ParentMapCheck 13
    && tttLargeFiber10Block5Chunk0ParentMapCheck 14
    && tttLargeFiber10Block5Chunk0ParentMapCheck 15

theorem tttLargeFiber10Block5Chunk0ParentMapAudit_ok :
    tttLargeFiber10Block5Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber10Block5Chunk0ParentMapAudit,
    tttLargeFiber10Block5Chunk0ParentMap_0_ok,
    tttLargeFiber10Block5Chunk0ParentMap_1_ok,
    tttLargeFiber10Block5Chunk0ParentMap_2_ok,
    tttLargeFiber10Block5Chunk0ParentMap_3_ok,
    tttLargeFiber10Block5Chunk0ParentMap_4_ok,
    tttLargeFiber10Block5Chunk0ParentMap_5_ok,
    tttLargeFiber10Block5Chunk0ParentMap_6_ok,
    tttLargeFiber10Block5Chunk0ParentMap_7_ok,
    tttLargeFiber10Block5Chunk0ParentMap_8_ok,
    tttLargeFiber10Block5Chunk0ParentMap_9_ok,
    tttLargeFiber10Block5Chunk0ParentMap_10_ok,
    tttLargeFiber10Block5Chunk0ParentMap_11_ok,
    tttLargeFiber10Block5Chunk0ParentMap_12_ok,
    tttLargeFiber10Block5Chunk0ParentMap_13_ok,
    tttLargeFiber10Block5Chunk0ParentMap_14_ok,
    tttLargeFiber10Block5Chunk0ParentMap_15_ok]

def tttLargeFiber10Block5Chunk0ParentsAudit : Bool :=
  tttLargeFiber10Block5Chunk0ParentPathCheck 0
    && tttLargeFiber10Block5Chunk0ParentPathCheck 1
    && tttLargeFiber10Block5Chunk0ParentPathCheck 2
    && tttLargeFiber10Block5Chunk0ParentPathCheck 3
    && tttLargeFiber10Block5Chunk0ParentPathCheck 4
    && tttLargeFiber10Block5Chunk0ParentPathCheck 5
    && tttLargeFiber10Block5Chunk0ParentPathCheck 6
    && tttLargeFiber10Block5Chunk0ParentPathCheck 7
    && tttLargeFiber10Block5Chunk0ParentPathCheck 8
    && tttLargeFiber10Block5Chunk0ParentPathCheck 9
    && tttLargeFiber10Block5Chunk0ParentPathCheck 10
    && tttLargeFiber10Block5Chunk0ParentPathCheck 11
    && tttLargeFiber10Block5Chunk0ParentPathCheck 12
    && tttLargeFiber10Block5Chunk0ParentPathCheck 13
    && tttLargeFiber10Block5Chunk0ParentPathCheck 14
    && tttLargeFiber10Block5Chunk0ParentPathCheck 15

theorem tttLargeFiber10Block5Chunk0ParentsAudit_ok :
    tttLargeFiber10Block5Chunk0ParentsAudit = true := by
  simp [tttLargeFiber10Block5Chunk0ParentsAudit,
    tttLargeFiber10Block5Chunk0ParentPath_0_ok,
    tttLargeFiber10Block5Chunk0ParentPath_1_ok,
    tttLargeFiber10Block5Chunk0ParentPath_2_ok,
    tttLargeFiber10Block5Chunk0ParentPath_3_ok,
    tttLargeFiber10Block5Chunk0ParentPath_4_ok,
    tttLargeFiber10Block5Chunk0ParentPath_5_ok,
    tttLargeFiber10Block5Chunk0ParentPath_6_ok,
    tttLargeFiber10Block5Chunk0ParentPath_7_ok,
    tttLargeFiber10Block5Chunk0ParentPath_8_ok,
    tttLargeFiber10Block5Chunk0ParentPath_9_ok,
    tttLargeFiber10Block5Chunk0ParentPath_10_ok,
    tttLargeFiber10Block5Chunk0ParentPath_11_ok,
    tttLargeFiber10Block5Chunk0ParentPath_12_ok,
    tttLargeFiber10Block5Chunk0ParentPath_13_ok,
    tttLargeFiber10Block5Chunk0ParentPath_14_ok,
    tttLargeFiber10Block5Chunk0ParentPath_15_ok]

def tttLargeFiber10Block5Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block5Chunk0SourcesCheck &&
    tttLargeFiber10Block5Chunk0RowsAudit &&
    tttLargeFiber10Block5Chunk0ParentMapAudit &&
    tttLargeFiber10Block5Chunk0ParentsAudit

theorem tttLargeFiber10Block5Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber10Block5Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block5Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block5Chunk0SourcesCheck_ok,
    tttLargeFiber10Block5Chunk0RowsAudit_ok,
    tttLargeFiber10Block5Chunk0ParentMapAudit_ok,
    tttLargeFiber10Block5Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block5Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
