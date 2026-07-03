import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 4 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block4Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block4Chunk3Sources : List Nat :=
  [   1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959,
   1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967]

def tttLargeFiber36Row304 : TripleComponentParentRow :=
  tripleRow 1952 320 56 166 64 8 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row305 : TripleComponentParentRow :=
  tripleRow 1953 321 56 166 65 8 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row306 : TripleComponentParentRow :=
  tripleRow 1954 322 56 166 66 8 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row307 : TripleComponentParentRow :=
  tripleRow 1955 1939 56 166 67 56 164 135
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

def tttLargeFiber36Row308 : TripleComponentParentRow :=
  tripleRow 1956 1924 56 166 116 56 150 48
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

def tttLargeFiber36Row309 : TripleComponentParentRow :=
  tripleRow 1957 1925 56 166 117 56 150 49
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

def tttLargeFiber36Row310 : TripleComponentParentRow :=
  tripleRow 1958 326 56 166 118 8 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row311 : TripleComponentParentRow :=
  tripleRow 1959 327 56 166 119 8 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row312 : TripleComponentParentRow :=
  tripleRow 1960 328 56 167 72 8 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row313 : TripleComponentParentRow :=
  tripleRow 1961 329 56 167 73 8 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row314 : TripleComponentParentRow :=
  tripleRow 1962 330 56 167 74 8 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row315 : TripleComponentParentRow :=
  tripleRow 1963 331 56 167 75 8 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row316 : TripleComponentParentRow :=
  tripleRow 1964 1932 56 167 124 56 151 56
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

def tttLargeFiber36Row317 : TripleComponentParentRow :=
  tripleRow 1965 1933 56 167 125 56 151 57
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

def tttLargeFiber36Row318 : TripleComponentParentRow :=
  tripleRow 1966 334 56 167 126 8 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row319 : TripleComponentParentRow :=
  tripleRow 1967 335 56 167 127 8 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Block4Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row304
  , tttLargeFiber36Row305
  , tttLargeFiber36Row306
  , tttLargeFiber36Row307
  , tttLargeFiber36Row308
  , tttLargeFiber36Row309
  , tttLargeFiber36Row310
  , tttLargeFiber36Row311
  , tttLargeFiber36Row312
  , tttLargeFiber36Row313
  , tttLargeFiber36Row314
  , tttLargeFiber36Row315
  , tttLargeFiber36Row316
  , tttLargeFiber36Row317
  , tttLargeFiber36Row318
  , tttLargeFiber36Row319
  ]

def tttLargeFiber36Block4Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block4Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block4Chunk3ExpectedContains row.source &&
    tttLargeFiber36Block4Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block4Chunk3SourcesCheck : Bool :=
  (tttLargeFiber36Block4Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber36Block4Chunk3Sources

theorem tttLargeFiber36Block4Chunk3SourcesCheck_ok :
    tttLargeFiber36Block4Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber36Block4Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block4Chunk3RowValid
    (listGetD tttLargeFiber36Block4Chunk3Rows i default)

def tttLargeFiber36Block4Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block4Chunk3Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block4Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block4Chunk3Sources 0 0 == 1952
      && tttLargeFiber36ParentOf 1952 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block4Chunk3Sources 1 0 == 1953
      && tttLargeFiber36ParentOf 1953 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block4Chunk3Sources 2 0 == 1954
      && tttLargeFiber36ParentOf 1954 == 322
      && tttLargeFiber36ParentOf 322 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block4Chunk3Sources 3 0 == 1955
      && tttLargeFiber36ParentOf 1955 == 1939
      && tttLargeFiber36ParentOf 1939 == 1907
      && tttLargeFiber36ParentOf 1907 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block4Chunk3Sources 4 0 == 1956
      && tttLargeFiber36ParentOf 1956 == 1924
      && tttLargeFiber36ParentOf 1924 == 1912
      && tttLargeFiber36ParentOf 1912 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block4Chunk3Sources 5 0 == 1957
      && tttLargeFiber36ParentOf 1957 == 1925
      && tttLargeFiber36ParentOf 1925 == 1913
      && tttLargeFiber36ParentOf 1913 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block4Chunk3Sources 6 0 == 1958
      && tttLargeFiber36ParentOf 1958 == 326
      && tttLargeFiber36ParentOf 326 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block4Chunk3Sources 7 0 == 1959
      && tttLargeFiber36ParentOf 1959 == 327
      && tttLargeFiber36ParentOf 327 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block4Chunk3Sources 8 0 == 1960
      && tttLargeFiber36ParentOf 1960 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block4Chunk3Sources 9 0 == 1961
      && tttLargeFiber36ParentOf 1961 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block4Chunk3Sources 10 0 == 1962
      && tttLargeFiber36ParentOf 1962 == 330
      && tttLargeFiber36ParentOf 330 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block4Chunk3Sources 11 0 == 1963
      && tttLargeFiber36ParentOf 1963 == 331
      && tttLargeFiber36ParentOf 331 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block4Chunk3Sources 12 0 == 1964
      && tttLargeFiber36ParentOf 1964 == 1932
      && tttLargeFiber36ParentOf 1932 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block4Chunk3Sources 13 0 == 1965
      && tttLargeFiber36ParentOf 1965 == 1933
      && tttLargeFiber36ParentOf 1933 == 1905
      && tttLargeFiber36ParentOf 1905 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block4Chunk3Sources 14 0 == 1966
      && tttLargeFiber36ParentOf 1966 == 334
      && tttLargeFiber36ParentOf 334 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block4Chunk3Sources 15 0 == 1967
      && tttLargeFiber36ParentOf 1967 == 335
      && tttLargeFiber36ParentOf 335 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block4Chunk3Row_0_ok :
    tttLargeFiber36Block4Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_1_ok :
    tttLargeFiber36Block4Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_2_ok :
    tttLargeFiber36Block4Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_3_ok :
    tttLargeFiber36Block4Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_4_ok :
    tttLargeFiber36Block4Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_5_ok :
    tttLargeFiber36Block4Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_6_ok :
    tttLargeFiber36Block4Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_7_ok :
    tttLargeFiber36Block4Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_8_ok :
    tttLargeFiber36Block4Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_9_ok :
    tttLargeFiber36Block4Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_10_ok :
    tttLargeFiber36Block4Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_11_ok :
    tttLargeFiber36Block4Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_12_ok :
    tttLargeFiber36Block4Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_13_ok :
    tttLargeFiber36Block4Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_14_ok :
    tttLargeFiber36Block4Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3Row_15_ok :
    tttLargeFiber36Block4Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_0_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_1_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_2_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_3_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_4_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_5_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_6_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_7_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_8_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_9_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_10_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_11_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_12_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_13_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_14_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentMap_15_ok :
    tttLargeFiber36Block4Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_0_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_1_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_2_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_3_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_4_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_5_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_6_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_7_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_8_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_9_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_10_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_11_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_12_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_13_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_14_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk3ParentPath_15_ok :
    tttLargeFiber36Block4Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block4Chunk3RowsAudit : Bool :=
  tttLargeFiber36Block4Chunk3RowCheck 0
    && tttLargeFiber36Block4Chunk3RowCheck 1
    && tttLargeFiber36Block4Chunk3RowCheck 2
    && tttLargeFiber36Block4Chunk3RowCheck 3
    && tttLargeFiber36Block4Chunk3RowCheck 4
    && tttLargeFiber36Block4Chunk3RowCheck 5
    && tttLargeFiber36Block4Chunk3RowCheck 6
    && tttLargeFiber36Block4Chunk3RowCheck 7
    && tttLargeFiber36Block4Chunk3RowCheck 8
    && tttLargeFiber36Block4Chunk3RowCheck 9
    && tttLargeFiber36Block4Chunk3RowCheck 10
    && tttLargeFiber36Block4Chunk3RowCheck 11
    && tttLargeFiber36Block4Chunk3RowCheck 12
    && tttLargeFiber36Block4Chunk3RowCheck 13
    && tttLargeFiber36Block4Chunk3RowCheck 14
    && tttLargeFiber36Block4Chunk3RowCheck 15

theorem tttLargeFiber36Block4Chunk3RowsAudit_ok :
    tttLargeFiber36Block4Chunk3RowsAudit = true := by
  simp [tttLargeFiber36Block4Chunk3RowsAudit,
    tttLargeFiber36Block4Chunk3Row_0_ok,
    tttLargeFiber36Block4Chunk3Row_1_ok,
    tttLargeFiber36Block4Chunk3Row_2_ok,
    tttLargeFiber36Block4Chunk3Row_3_ok,
    tttLargeFiber36Block4Chunk3Row_4_ok,
    tttLargeFiber36Block4Chunk3Row_5_ok,
    tttLargeFiber36Block4Chunk3Row_6_ok,
    tttLargeFiber36Block4Chunk3Row_7_ok,
    tttLargeFiber36Block4Chunk3Row_8_ok,
    tttLargeFiber36Block4Chunk3Row_9_ok,
    tttLargeFiber36Block4Chunk3Row_10_ok,
    tttLargeFiber36Block4Chunk3Row_11_ok,
    tttLargeFiber36Block4Chunk3Row_12_ok,
    tttLargeFiber36Block4Chunk3Row_13_ok,
    tttLargeFiber36Block4Chunk3Row_14_ok,
    tttLargeFiber36Block4Chunk3Row_15_ok]

def tttLargeFiber36Block4Chunk3ParentMapAudit : Bool :=
  tttLargeFiber36Block4Chunk3ParentMapCheck 0
    && tttLargeFiber36Block4Chunk3ParentMapCheck 1
    && tttLargeFiber36Block4Chunk3ParentMapCheck 2
    && tttLargeFiber36Block4Chunk3ParentMapCheck 3
    && tttLargeFiber36Block4Chunk3ParentMapCheck 4
    && tttLargeFiber36Block4Chunk3ParentMapCheck 5
    && tttLargeFiber36Block4Chunk3ParentMapCheck 6
    && tttLargeFiber36Block4Chunk3ParentMapCheck 7
    && tttLargeFiber36Block4Chunk3ParentMapCheck 8
    && tttLargeFiber36Block4Chunk3ParentMapCheck 9
    && tttLargeFiber36Block4Chunk3ParentMapCheck 10
    && tttLargeFiber36Block4Chunk3ParentMapCheck 11
    && tttLargeFiber36Block4Chunk3ParentMapCheck 12
    && tttLargeFiber36Block4Chunk3ParentMapCheck 13
    && tttLargeFiber36Block4Chunk3ParentMapCheck 14
    && tttLargeFiber36Block4Chunk3ParentMapCheck 15

theorem tttLargeFiber36Block4Chunk3ParentMapAudit_ok :
    tttLargeFiber36Block4Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber36Block4Chunk3ParentMapAudit,
    tttLargeFiber36Block4Chunk3ParentMap_0_ok,
    tttLargeFiber36Block4Chunk3ParentMap_1_ok,
    tttLargeFiber36Block4Chunk3ParentMap_2_ok,
    tttLargeFiber36Block4Chunk3ParentMap_3_ok,
    tttLargeFiber36Block4Chunk3ParentMap_4_ok,
    tttLargeFiber36Block4Chunk3ParentMap_5_ok,
    tttLargeFiber36Block4Chunk3ParentMap_6_ok,
    tttLargeFiber36Block4Chunk3ParentMap_7_ok,
    tttLargeFiber36Block4Chunk3ParentMap_8_ok,
    tttLargeFiber36Block4Chunk3ParentMap_9_ok,
    tttLargeFiber36Block4Chunk3ParentMap_10_ok,
    tttLargeFiber36Block4Chunk3ParentMap_11_ok,
    tttLargeFiber36Block4Chunk3ParentMap_12_ok,
    tttLargeFiber36Block4Chunk3ParentMap_13_ok,
    tttLargeFiber36Block4Chunk3ParentMap_14_ok,
    tttLargeFiber36Block4Chunk3ParentMap_15_ok]

def tttLargeFiber36Block4Chunk3ParentsAudit : Bool :=
  tttLargeFiber36Block4Chunk3ParentPathCheck 0
    && tttLargeFiber36Block4Chunk3ParentPathCheck 1
    && tttLargeFiber36Block4Chunk3ParentPathCheck 2
    && tttLargeFiber36Block4Chunk3ParentPathCheck 3
    && tttLargeFiber36Block4Chunk3ParentPathCheck 4
    && tttLargeFiber36Block4Chunk3ParentPathCheck 5
    && tttLargeFiber36Block4Chunk3ParentPathCheck 6
    && tttLargeFiber36Block4Chunk3ParentPathCheck 7
    && tttLargeFiber36Block4Chunk3ParentPathCheck 8
    && tttLargeFiber36Block4Chunk3ParentPathCheck 9
    && tttLargeFiber36Block4Chunk3ParentPathCheck 10
    && tttLargeFiber36Block4Chunk3ParentPathCheck 11
    && tttLargeFiber36Block4Chunk3ParentPathCheck 12
    && tttLargeFiber36Block4Chunk3ParentPathCheck 13
    && tttLargeFiber36Block4Chunk3ParentPathCheck 14
    && tttLargeFiber36Block4Chunk3ParentPathCheck 15

theorem tttLargeFiber36Block4Chunk3ParentsAudit_ok :
    tttLargeFiber36Block4Chunk3ParentsAudit = true := by
  simp [tttLargeFiber36Block4Chunk3ParentsAudit,
    tttLargeFiber36Block4Chunk3ParentPath_0_ok,
    tttLargeFiber36Block4Chunk3ParentPath_1_ok,
    tttLargeFiber36Block4Chunk3ParentPath_2_ok,
    tttLargeFiber36Block4Chunk3ParentPath_3_ok,
    tttLargeFiber36Block4Chunk3ParentPath_4_ok,
    tttLargeFiber36Block4Chunk3ParentPath_5_ok,
    tttLargeFiber36Block4Chunk3ParentPath_6_ok,
    tttLargeFiber36Block4Chunk3ParentPath_7_ok,
    tttLargeFiber36Block4Chunk3ParentPath_8_ok,
    tttLargeFiber36Block4Chunk3ParentPath_9_ok,
    tttLargeFiber36Block4Chunk3ParentPath_10_ok,
    tttLargeFiber36Block4Chunk3ParentPath_11_ok,
    tttLargeFiber36Block4Chunk3ParentPath_12_ok,
    tttLargeFiber36Block4Chunk3ParentPath_13_ok,
    tttLargeFiber36Block4Chunk3ParentPath_14_ok,
    tttLargeFiber36Block4Chunk3ParentPath_15_ok]

def tttLargeFiber36Block4Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block4Chunk3SourcesCheck &&
    tttLargeFiber36Block4Chunk3RowsAudit &&
    tttLargeFiber36Block4Chunk3ParentMapAudit &&
    tttLargeFiber36Block4Chunk3ParentsAudit

theorem tttLargeFiber36Block4Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber36Block4Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block4Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block4Chunk3SourcesCheck_ok,
    tttLargeFiber36Block4Chunk3RowsAudit_ok,
    tttLargeFiber36Block4Chunk3ParentMapAudit_ok,
    tttLargeFiber36Block4Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block4Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
