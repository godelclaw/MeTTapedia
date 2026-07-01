import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 5 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block5Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block5Chunk0Sources : List Nat :=
  [   1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975,
   1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]

def tttLargeFiber36Row320 : TripleComponentParentRow :=
  tripleRow 1968 336 57 156 148 9 88 80
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

def tttLargeFiber36Row321 : TripleComponentParentRow :=
  tripleRow 1969 337 57 156 149 9 88 81
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

def tttLargeFiber36Row322 : TripleComponentParentRow :=
  tripleRow 1970 338 57 156 150 9 88 82
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

def tttLargeFiber36Row323 : TripleComponentParentRow :=
  tripleRow 1971 1968 57 156 151 57 156 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row324 : TripleComponentParentRow :=
  tripleRow 1972 1968 57 156 164 57 156 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row325 : TripleComponentParentRow :=
  tripleRow 1973 1969 57 156 165 57 156 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row326 : TripleComponentParentRow :=
  tripleRow 1974 342 57 156 166 9 88 102
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

def tttLargeFiber36Row327 : TripleComponentParentRow :=
  tripleRow 1975 343 57 156 167 9 88 103
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

def tttLargeFiber36Row328 : TripleComponentParentRow :=
  tripleRow 1976 344 57 157 156 9 89 88
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

def tttLargeFiber36Row329 : TripleComponentParentRow :=
  tripleRow 1977 345 57 157 157 9 89 89
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

def tttLargeFiber36Row330 : TripleComponentParentRow :=
  tripleRow 1978 346 57 157 158 9 89 90
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

def tttLargeFiber36Row331 : TripleComponentParentRow :=
  tripleRow 1979 1976 57 157 159 57 157 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row332 : TripleComponentParentRow :=
  tripleRow 1980 1976 57 157 172 57 157 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row333 : TripleComponentParentRow :=
  tripleRow 1981 1977 57 157 173 57 157 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row334 : TripleComponentParentRow :=
  tripleRow 1982 350 57 157 174 9 89 110
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

def tttLargeFiber36Row335 : TripleComponentParentRow :=
  tripleRow 1983 351 57 157 175 9 89 111
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

def tttLargeFiber36Block5Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row320
  , tttLargeFiber36Row321
  , tttLargeFiber36Row322
  , tttLargeFiber36Row323
  , tttLargeFiber36Row324
  , tttLargeFiber36Row325
  , tttLargeFiber36Row326
  , tttLargeFiber36Row327
  , tttLargeFiber36Row328
  , tttLargeFiber36Row329
  , tttLargeFiber36Row330
  , tttLargeFiber36Row331
  , tttLargeFiber36Row332
  , tttLargeFiber36Row333
  , tttLargeFiber36Row334
  , tttLargeFiber36Row335
  ]

def tttLargeFiber36Block5Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block5Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block5Chunk0ExpectedContains row.source &&
    tttLargeFiber36Block5Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block5Chunk0SourcesCheck : Bool :=
  (tttLargeFiber36Block5Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber36Block5Chunk0Sources

theorem tttLargeFiber36Block5Chunk0SourcesCheck_ok :
    tttLargeFiber36Block5Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber36Block5Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block5Chunk0RowValid
    (listGetD tttLargeFiber36Block5Chunk0Rows i default)

def tttLargeFiber36Block5Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block5Chunk0Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block5Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block5Chunk0Sources 0 0 == 1968
      && tttLargeFiber36ParentOf 1968 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block5Chunk0Sources 1 0 == 1969
      && tttLargeFiber36ParentOf 1969 == 337
      && tttLargeFiber36ParentOf 337 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block5Chunk0Sources 2 0 == 1970
      && tttLargeFiber36ParentOf 1970 == 338
      && tttLargeFiber36ParentOf 338 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block5Chunk0Sources 3 0 == 1971
      && tttLargeFiber36ParentOf 1971 == 1968
      && tttLargeFiber36ParentOf 1968 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block5Chunk0Sources 4 0 == 1972
      && tttLargeFiber36ParentOf 1972 == 1968
      && tttLargeFiber36ParentOf 1968 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block5Chunk0Sources 5 0 == 1973
      && tttLargeFiber36ParentOf 1973 == 1969
      && tttLargeFiber36ParentOf 1969 == 337
      && tttLargeFiber36ParentOf 337 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block5Chunk0Sources 6 0 == 1974
      && tttLargeFiber36ParentOf 1974 == 342
      && tttLargeFiber36ParentOf 342 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block5Chunk0Sources 7 0 == 1975
      && tttLargeFiber36ParentOf 1975 == 343
      && tttLargeFiber36ParentOf 343 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block5Chunk0Sources 8 0 == 1976
      && tttLargeFiber36ParentOf 1976 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block5Chunk0Sources 9 0 == 1977
      && tttLargeFiber36ParentOf 1977 == 345
      && tttLargeFiber36ParentOf 345 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block5Chunk0Sources 10 0 == 1978
      && tttLargeFiber36ParentOf 1978 == 346
      && tttLargeFiber36ParentOf 346 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block5Chunk0Sources 11 0 == 1979
      && tttLargeFiber36ParentOf 1979 == 1976
      && tttLargeFiber36ParentOf 1976 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block5Chunk0Sources 12 0 == 1980
      && tttLargeFiber36ParentOf 1980 == 1976
      && tttLargeFiber36ParentOf 1976 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block5Chunk0Sources 13 0 == 1981
      && tttLargeFiber36ParentOf 1981 == 1977
      && tttLargeFiber36ParentOf 1977 == 345
      && tttLargeFiber36ParentOf 345 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block5Chunk0Sources 14 0 == 1982
      && tttLargeFiber36ParentOf 1982 == 350
      && tttLargeFiber36ParentOf 350 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block5Chunk0Sources 15 0 == 1983
      && tttLargeFiber36ParentOf 1983 == 351
      && tttLargeFiber36ParentOf 351 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block5Chunk0Row_0_ok :
    tttLargeFiber36Block5Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_1_ok :
    tttLargeFiber36Block5Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_2_ok :
    tttLargeFiber36Block5Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_3_ok :
    tttLargeFiber36Block5Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_4_ok :
    tttLargeFiber36Block5Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_5_ok :
    tttLargeFiber36Block5Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_6_ok :
    tttLargeFiber36Block5Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_7_ok :
    tttLargeFiber36Block5Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_8_ok :
    tttLargeFiber36Block5Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_9_ok :
    tttLargeFiber36Block5Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_10_ok :
    tttLargeFiber36Block5Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_11_ok :
    tttLargeFiber36Block5Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_12_ok :
    tttLargeFiber36Block5Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_13_ok :
    tttLargeFiber36Block5Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_14_ok :
    tttLargeFiber36Block5Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0Row_15_ok :
    tttLargeFiber36Block5Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_0_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_1_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_2_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_3_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_4_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_5_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_6_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_7_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_8_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_9_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_10_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_11_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_12_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_13_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_14_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentMap_15_ok :
    tttLargeFiber36Block5Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_0_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_1_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_2_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_3_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_4_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_5_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_6_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_7_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_8_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_9_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_10_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_11_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_12_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_13_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_14_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block5Chunk0ParentPath_15_ok :
    tttLargeFiber36Block5Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block5Chunk0RowsAudit : Bool :=
  tttLargeFiber36Block5Chunk0RowCheck 0
    && tttLargeFiber36Block5Chunk0RowCheck 1
    && tttLargeFiber36Block5Chunk0RowCheck 2
    && tttLargeFiber36Block5Chunk0RowCheck 3
    && tttLargeFiber36Block5Chunk0RowCheck 4
    && tttLargeFiber36Block5Chunk0RowCheck 5
    && tttLargeFiber36Block5Chunk0RowCheck 6
    && tttLargeFiber36Block5Chunk0RowCheck 7
    && tttLargeFiber36Block5Chunk0RowCheck 8
    && tttLargeFiber36Block5Chunk0RowCheck 9
    && tttLargeFiber36Block5Chunk0RowCheck 10
    && tttLargeFiber36Block5Chunk0RowCheck 11
    && tttLargeFiber36Block5Chunk0RowCheck 12
    && tttLargeFiber36Block5Chunk0RowCheck 13
    && tttLargeFiber36Block5Chunk0RowCheck 14
    && tttLargeFiber36Block5Chunk0RowCheck 15

theorem tttLargeFiber36Block5Chunk0RowsAudit_ok :
    tttLargeFiber36Block5Chunk0RowsAudit = true := by
  simp [tttLargeFiber36Block5Chunk0RowsAudit,
    tttLargeFiber36Block5Chunk0Row_0_ok,
    tttLargeFiber36Block5Chunk0Row_1_ok,
    tttLargeFiber36Block5Chunk0Row_2_ok,
    tttLargeFiber36Block5Chunk0Row_3_ok,
    tttLargeFiber36Block5Chunk0Row_4_ok,
    tttLargeFiber36Block5Chunk0Row_5_ok,
    tttLargeFiber36Block5Chunk0Row_6_ok,
    tttLargeFiber36Block5Chunk0Row_7_ok,
    tttLargeFiber36Block5Chunk0Row_8_ok,
    tttLargeFiber36Block5Chunk0Row_9_ok,
    tttLargeFiber36Block5Chunk0Row_10_ok,
    tttLargeFiber36Block5Chunk0Row_11_ok,
    tttLargeFiber36Block5Chunk0Row_12_ok,
    tttLargeFiber36Block5Chunk0Row_13_ok,
    tttLargeFiber36Block5Chunk0Row_14_ok,
    tttLargeFiber36Block5Chunk0Row_15_ok]

def tttLargeFiber36Block5Chunk0ParentMapAudit : Bool :=
  tttLargeFiber36Block5Chunk0ParentMapCheck 0
    && tttLargeFiber36Block5Chunk0ParentMapCheck 1
    && tttLargeFiber36Block5Chunk0ParentMapCheck 2
    && tttLargeFiber36Block5Chunk0ParentMapCheck 3
    && tttLargeFiber36Block5Chunk0ParentMapCheck 4
    && tttLargeFiber36Block5Chunk0ParentMapCheck 5
    && tttLargeFiber36Block5Chunk0ParentMapCheck 6
    && tttLargeFiber36Block5Chunk0ParentMapCheck 7
    && tttLargeFiber36Block5Chunk0ParentMapCheck 8
    && tttLargeFiber36Block5Chunk0ParentMapCheck 9
    && tttLargeFiber36Block5Chunk0ParentMapCheck 10
    && tttLargeFiber36Block5Chunk0ParentMapCheck 11
    && tttLargeFiber36Block5Chunk0ParentMapCheck 12
    && tttLargeFiber36Block5Chunk0ParentMapCheck 13
    && tttLargeFiber36Block5Chunk0ParentMapCheck 14
    && tttLargeFiber36Block5Chunk0ParentMapCheck 15

theorem tttLargeFiber36Block5Chunk0ParentMapAudit_ok :
    tttLargeFiber36Block5Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber36Block5Chunk0ParentMapAudit,
    tttLargeFiber36Block5Chunk0ParentMap_0_ok,
    tttLargeFiber36Block5Chunk0ParentMap_1_ok,
    tttLargeFiber36Block5Chunk0ParentMap_2_ok,
    tttLargeFiber36Block5Chunk0ParentMap_3_ok,
    tttLargeFiber36Block5Chunk0ParentMap_4_ok,
    tttLargeFiber36Block5Chunk0ParentMap_5_ok,
    tttLargeFiber36Block5Chunk0ParentMap_6_ok,
    tttLargeFiber36Block5Chunk0ParentMap_7_ok,
    tttLargeFiber36Block5Chunk0ParentMap_8_ok,
    tttLargeFiber36Block5Chunk0ParentMap_9_ok,
    tttLargeFiber36Block5Chunk0ParentMap_10_ok,
    tttLargeFiber36Block5Chunk0ParentMap_11_ok,
    tttLargeFiber36Block5Chunk0ParentMap_12_ok,
    tttLargeFiber36Block5Chunk0ParentMap_13_ok,
    tttLargeFiber36Block5Chunk0ParentMap_14_ok,
    tttLargeFiber36Block5Chunk0ParentMap_15_ok]

def tttLargeFiber36Block5Chunk0ParentsAudit : Bool :=
  tttLargeFiber36Block5Chunk0ParentPathCheck 0
    && tttLargeFiber36Block5Chunk0ParentPathCheck 1
    && tttLargeFiber36Block5Chunk0ParentPathCheck 2
    && tttLargeFiber36Block5Chunk0ParentPathCheck 3
    && tttLargeFiber36Block5Chunk0ParentPathCheck 4
    && tttLargeFiber36Block5Chunk0ParentPathCheck 5
    && tttLargeFiber36Block5Chunk0ParentPathCheck 6
    && tttLargeFiber36Block5Chunk0ParentPathCheck 7
    && tttLargeFiber36Block5Chunk0ParentPathCheck 8
    && tttLargeFiber36Block5Chunk0ParentPathCheck 9
    && tttLargeFiber36Block5Chunk0ParentPathCheck 10
    && tttLargeFiber36Block5Chunk0ParentPathCheck 11
    && tttLargeFiber36Block5Chunk0ParentPathCheck 12
    && tttLargeFiber36Block5Chunk0ParentPathCheck 13
    && tttLargeFiber36Block5Chunk0ParentPathCheck 14
    && tttLargeFiber36Block5Chunk0ParentPathCheck 15

theorem tttLargeFiber36Block5Chunk0ParentsAudit_ok :
    tttLargeFiber36Block5Chunk0ParentsAudit = true := by
  simp [tttLargeFiber36Block5Chunk0ParentsAudit,
    tttLargeFiber36Block5Chunk0ParentPath_0_ok,
    tttLargeFiber36Block5Chunk0ParentPath_1_ok,
    tttLargeFiber36Block5Chunk0ParentPath_2_ok,
    tttLargeFiber36Block5Chunk0ParentPath_3_ok,
    tttLargeFiber36Block5Chunk0ParentPath_4_ok,
    tttLargeFiber36Block5Chunk0ParentPath_5_ok,
    tttLargeFiber36Block5Chunk0ParentPath_6_ok,
    tttLargeFiber36Block5Chunk0ParentPath_7_ok,
    tttLargeFiber36Block5Chunk0ParentPath_8_ok,
    tttLargeFiber36Block5Chunk0ParentPath_9_ok,
    tttLargeFiber36Block5Chunk0ParentPath_10_ok,
    tttLargeFiber36Block5Chunk0ParentPath_11_ok,
    tttLargeFiber36Block5Chunk0ParentPath_12_ok,
    tttLargeFiber36Block5Chunk0ParentPath_13_ok,
    tttLargeFiber36Block5Chunk0ParentPath_14_ok,
    tttLargeFiber36Block5Chunk0ParentPath_15_ok]

def tttLargeFiber36Block5Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block5Chunk0SourcesCheck &&
    tttLargeFiber36Block5Chunk0RowsAudit &&
    tttLargeFiber36Block5Chunk0ParentMapAudit &&
    tttLargeFiber36Block5Chunk0ParentsAudit

theorem tttLargeFiber36Block5Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber36Block5Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block5Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block5Chunk0SourcesCheck_ok,
    tttLargeFiber36Block5Chunk0RowsAudit_ok,
    tttLargeFiber36Block5Chunk0ParentMapAudit_ok,
    tttLargeFiber36Block5Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block5Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
