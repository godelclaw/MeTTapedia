import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 4 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block4Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block4Chunk1Sources : List Nat :=
  [   1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927,
   1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]

def tttLargeFiber36Row272 : TripleComponentParentRow :=
  tripleRow 1920 288 56 150 0 8 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row273 : TripleComponentParentRow :=
  tripleRow 1921 289 56 150 1 8 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row274 : TripleComponentParentRow :=
  tripleRow 1922 290 56 150 2 8 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row275 : TripleComponentParentRow :=
  tripleRow 1923 291 56 150 3 8 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row276 : TripleComponentParentRow :=
  tripleRow 1924 1912 56 150 48 56 149 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row277 : TripleComponentParentRow :=
  tripleRow 1925 1913 56 150 49 56 149 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row278 : TripleComponentParentRow :=
  tripleRow 1926 294 56 150 50 8 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row279 : TripleComponentParentRow :=
  tripleRow 1927 295 56 150 51 8 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row280 : TripleComponentParentRow :=
  tripleRow 1928 1911 56 151 8 56 148 167
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row281 : TripleComponentParentRow :=
  tripleRow 1929 1910 56 151 9 56 148 166
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
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

def tttLargeFiber36Row282 : TripleComponentParentRow :=
  tripleRow 1930 1908 56 151 10 56 148 164
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row283 : TripleComponentParentRow :=
  tripleRow 1931 1909 56 151 11 56 148 165
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row284 : TripleComponentParentRow :=
  tripleRow 1932 1904 56 151 56 56 148 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row285 : TripleComponentParentRow :=
  tripleRow 1933 1905 56 151 57 56 148 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row286 : TripleComponentParentRow :=
  tripleRow 1934 1906 56 151 58 56 148 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Row287 : TripleComponentParentRow :=
  tripleRow 1935 1907 56 151 59 56 148 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber36Block4Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row272
  , tttLargeFiber36Row273
  , tttLargeFiber36Row274
  , tttLargeFiber36Row275
  , tttLargeFiber36Row276
  , tttLargeFiber36Row277
  , tttLargeFiber36Row278
  , tttLargeFiber36Row279
  , tttLargeFiber36Row280
  , tttLargeFiber36Row281
  , tttLargeFiber36Row282
  , tttLargeFiber36Row283
  , tttLargeFiber36Row284
  , tttLargeFiber36Row285
  , tttLargeFiber36Row286
  , tttLargeFiber36Row287
  ]

def tttLargeFiber36Block4Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block4Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block4Chunk1ExpectedContains row.source &&
    tttLargeFiber36Block4Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block4Chunk1SourcesCheck : Bool :=
  (tttLargeFiber36Block4Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber36Block4Chunk1Sources

theorem tttLargeFiber36Block4Chunk1SourcesCheck_ok :
    tttLargeFiber36Block4Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber36Block4Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block4Chunk1RowValid
    (listGetD tttLargeFiber36Block4Chunk1Rows i default)

def tttLargeFiber36Block4Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block4Chunk1Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block4Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block4Chunk1Sources 0 0 == 1920
      && tttLargeFiber36ParentOf 1920 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block4Chunk1Sources 1 0 == 1921
      && tttLargeFiber36ParentOf 1921 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block4Chunk1Sources 2 0 == 1922
      && tttLargeFiber36ParentOf 1922 == 290
      && tttLargeFiber36ParentOf 290 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block4Chunk1Sources 3 0 == 1923
      && tttLargeFiber36ParentOf 1923 == 291
      && tttLargeFiber36ParentOf 291 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block4Chunk1Sources 4 0 == 1924
      && tttLargeFiber36ParentOf 1924 == 1912
      && tttLargeFiber36ParentOf 1912 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block4Chunk1Sources 5 0 == 1925
      && tttLargeFiber36ParentOf 1925 == 1913
      && tttLargeFiber36ParentOf 1913 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block4Chunk1Sources 6 0 == 1926
      && tttLargeFiber36ParentOf 1926 == 294
      && tttLargeFiber36ParentOf 294 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block4Chunk1Sources 7 0 == 1927
      && tttLargeFiber36ParentOf 1927 == 295
      && tttLargeFiber36ParentOf 295 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block4Chunk1Sources 8 0 == 1928
      && tttLargeFiber36ParentOf 1928 == 1911
      && tttLargeFiber36ParentOf 1911 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block4Chunk1Sources 9 0 == 1929
      && tttLargeFiber36ParentOf 1929 == 1910
      && tttLargeFiber36ParentOf 1910 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block4Chunk1Sources 10 0 == 1930
      && tttLargeFiber36ParentOf 1930 == 1908
      && tttLargeFiber36ParentOf 1908 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block4Chunk1Sources 11 0 == 1931
      && tttLargeFiber36ParentOf 1931 == 1909
      && tttLargeFiber36ParentOf 1909 == 1905
      && tttLargeFiber36ParentOf 1905 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block4Chunk1Sources 12 0 == 1932
      && tttLargeFiber36ParentOf 1932 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block4Chunk1Sources 13 0 == 1933
      && tttLargeFiber36ParentOf 1933 == 1905
      && tttLargeFiber36ParentOf 1905 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block4Chunk1Sources 14 0 == 1934
      && tttLargeFiber36ParentOf 1934 == 1906
      && tttLargeFiber36ParentOf 1906 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block4Chunk1Sources 15 0 == 1935
      && tttLargeFiber36ParentOf 1935 == 1907
      && tttLargeFiber36ParentOf 1907 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block4Chunk1Row_0_ok :
    tttLargeFiber36Block4Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_1_ok :
    tttLargeFiber36Block4Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_2_ok :
    tttLargeFiber36Block4Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_3_ok :
    tttLargeFiber36Block4Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_4_ok :
    tttLargeFiber36Block4Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_5_ok :
    tttLargeFiber36Block4Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_6_ok :
    tttLargeFiber36Block4Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_7_ok :
    tttLargeFiber36Block4Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_8_ok :
    tttLargeFiber36Block4Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_9_ok :
    tttLargeFiber36Block4Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_10_ok :
    tttLargeFiber36Block4Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_11_ok :
    tttLargeFiber36Block4Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_12_ok :
    tttLargeFiber36Block4Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_13_ok :
    tttLargeFiber36Block4Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_14_ok :
    tttLargeFiber36Block4Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1Row_15_ok :
    tttLargeFiber36Block4Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_0_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_1_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_2_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_3_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_4_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_5_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_6_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_7_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_8_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_9_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_10_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_11_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_12_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_13_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_14_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentMap_15_ok :
    tttLargeFiber36Block4Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_0_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_1_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_2_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_3_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_4_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_5_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_6_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_7_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_8_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_9_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_10_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_11_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_12_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_13_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_14_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk1ParentPath_15_ok :
    tttLargeFiber36Block4Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block4Chunk1RowsAudit : Bool :=
  tttLargeFiber36Block4Chunk1RowCheck 0
    && tttLargeFiber36Block4Chunk1RowCheck 1
    && tttLargeFiber36Block4Chunk1RowCheck 2
    && tttLargeFiber36Block4Chunk1RowCheck 3
    && tttLargeFiber36Block4Chunk1RowCheck 4
    && tttLargeFiber36Block4Chunk1RowCheck 5
    && tttLargeFiber36Block4Chunk1RowCheck 6
    && tttLargeFiber36Block4Chunk1RowCheck 7
    && tttLargeFiber36Block4Chunk1RowCheck 8
    && tttLargeFiber36Block4Chunk1RowCheck 9
    && tttLargeFiber36Block4Chunk1RowCheck 10
    && tttLargeFiber36Block4Chunk1RowCheck 11
    && tttLargeFiber36Block4Chunk1RowCheck 12
    && tttLargeFiber36Block4Chunk1RowCheck 13
    && tttLargeFiber36Block4Chunk1RowCheck 14
    && tttLargeFiber36Block4Chunk1RowCheck 15

theorem tttLargeFiber36Block4Chunk1RowsAudit_ok :
    tttLargeFiber36Block4Chunk1RowsAudit = true := by
  simp [tttLargeFiber36Block4Chunk1RowsAudit,
    tttLargeFiber36Block4Chunk1Row_0_ok,
    tttLargeFiber36Block4Chunk1Row_1_ok,
    tttLargeFiber36Block4Chunk1Row_2_ok,
    tttLargeFiber36Block4Chunk1Row_3_ok,
    tttLargeFiber36Block4Chunk1Row_4_ok,
    tttLargeFiber36Block4Chunk1Row_5_ok,
    tttLargeFiber36Block4Chunk1Row_6_ok,
    tttLargeFiber36Block4Chunk1Row_7_ok,
    tttLargeFiber36Block4Chunk1Row_8_ok,
    tttLargeFiber36Block4Chunk1Row_9_ok,
    tttLargeFiber36Block4Chunk1Row_10_ok,
    tttLargeFiber36Block4Chunk1Row_11_ok,
    tttLargeFiber36Block4Chunk1Row_12_ok,
    tttLargeFiber36Block4Chunk1Row_13_ok,
    tttLargeFiber36Block4Chunk1Row_14_ok,
    tttLargeFiber36Block4Chunk1Row_15_ok]

def tttLargeFiber36Block4Chunk1ParentMapAudit : Bool :=
  tttLargeFiber36Block4Chunk1ParentMapCheck 0
    && tttLargeFiber36Block4Chunk1ParentMapCheck 1
    && tttLargeFiber36Block4Chunk1ParentMapCheck 2
    && tttLargeFiber36Block4Chunk1ParentMapCheck 3
    && tttLargeFiber36Block4Chunk1ParentMapCheck 4
    && tttLargeFiber36Block4Chunk1ParentMapCheck 5
    && tttLargeFiber36Block4Chunk1ParentMapCheck 6
    && tttLargeFiber36Block4Chunk1ParentMapCheck 7
    && tttLargeFiber36Block4Chunk1ParentMapCheck 8
    && tttLargeFiber36Block4Chunk1ParentMapCheck 9
    && tttLargeFiber36Block4Chunk1ParentMapCheck 10
    && tttLargeFiber36Block4Chunk1ParentMapCheck 11
    && tttLargeFiber36Block4Chunk1ParentMapCheck 12
    && tttLargeFiber36Block4Chunk1ParentMapCheck 13
    && tttLargeFiber36Block4Chunk1ParentMapCheck 14
    && tttLargeFiber36Block4Chunk1ParentMapCheck 15

theorem tttLargeFiber36Block4Chunk1ParentMapAudit_ok :
    tttLargeFiber36Block4Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber36Block4Chunk1ParentMapAudit,
    tttLargeFiber36Block4Chunk1ParentMap_0_ok,
    tttLargeFiber36Block4Chunk1ParentMap_1_ok,
    tttLargeFiber36Block4Chunk1ParentMap_2_ok,
    tttLargeFiber36Block4Chunk1ParentMap_3_ok,
    tttLargeFiber36Block4Chunk1ParentMap_4_ok,
    tttLargeFiber36Block4Chunk1ParentMap_5_ok,
    tttLargeFiber36Block4Chunk1ParentMap_6_ok,
    tttLargeFiber36Block4Chunk1ParentMap_7_ok,
    tttLargeFiber36Block4Chunk1ParentMap_8_ok,
    tttLargeFiber36Block4Chunk1ParentMap_9_ok,
    tttLargeFiber36Block4Chunk1ParentMap_10_ok,
    tttLargeFiber36Block4Chunk1ParentMap_11_ok,
    tttLargeFiber36Block4Chunk1ParentMap_12_ok,
    tttLargeFiber36Block4Chunk1ParentMap_13_ok,
    tttLargeFiber36Block4Chunk1ParentMap_14_ok,
    tttLargeFiber36Block4Chunk1ParentMap_15_ok]

def tttLargeFiber36Block4Chunk1ParentsAudit : Bool :=
  tttLargeFiber36Block4Chunk1ParentPathCheck 0
    && tttLargeFiber36Block4Chunk1ParentPathCheck 1
    && tttLargeFiber36Block4Chunk1ParentPathCheck 2
    && tttLargeFiber36Block4Chunk1ParentPathCheck 3
    && tttLargeFiber36Block4Chunk1ParentPathCheck 4
    && tttLargeFiber36Block4Chunk1ParentPathCheck 5
    && tttLargeFiber36Block4Chunk1ParentPathCheck 6
    && tttLargeFiber36Block4Chunk1ParentPathCheck 7
    && tttLargeFiber36Block4Chunk1ParentPathCheck 8
    && tttLargeFiber36Block4Chunk1ParentPathCheck 9
    && tttLargeFiber36Block4Chunk1ParentPathCheck 10
    && tttLargeFiber36Block4Chunk1ParentPathCheck 11
    && tttLargeFiber36Block4Chunk1ParentPathCheck 12
    && tttLargeFiber36Block4Chunk1ParentPathCheck 13
    && tttLargeFiber36Block4Chunk1ParentPathCheck 14
    && tttLargeFiber36Block4Chunk1ParentPathCheck 15

theorem tttLargeFiber36Block4Chunk1ParentsAudit_ok :
    tttLargeFiber36Block4Chunk1ParentsAudit = true := by
  simp [tttLargeFiber36Block4Chunk1ParentsAudit,
    tttLargeFiber36Block4Chunk1ParentPath_0_ok,
    tttLargeFiber36Block4Chunk1ParentPath_1_ok,
    tttLargeFiber36Block4Chunk1ParentPath_2_ok,
    tttLargeFiber36Block4Chunk1ParentPath_3_ok,
    tttLargeFiber36Block4Chunk1ParentPath_4_ok,
    tttLargeFiber36Block4Chunk1ParentPath_5_ok,
    tttLargeFiber36Block4Chunk1ParentPath_6_ok,
    tttLargeFiber36Block4Chunk1ParentPath_7_ok,
    tttLargeFiber36Block4Chunk1ParentPath_8_ok,
    tttLargeFiber36Block4Chunk1ParentPath_9_ok,
    tttLargeFiber36Block4Chunk1ParentPath_10_ok,
    tttLargeFiber36Block4Chunk1ParentPath_11_ok,
    tttLargeFiber36Block4Chunk1ParentPath_12_ok,
    tttLargeFiber36Block4Chunk1ParentPath_13_ok,
    tttLargeFiber36Block4Chunk1ParentPath_14_ok,
    tttLargeFiber36Block4Chunk1ParentPath_15_ok]

def tttLargeFiber36Block4Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block4Chunk1SourcesCheck &&
    tttLargeFiber36Block4Chunk1RowsAudit &&
    tttLargeFiber36Block4Chunk1ParentMapAudit &&
    tttLargeFiber36Block4Chunk1ParentsAudit

theorem tttLargeFiber36Block4Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber36Block4Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block4Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block4Chunk1SourcesCheck_ok,
    tttLargeFiber36Block4Chunk1RowsAudit_ok,
    tttLargeFiber36Block4Chunk1ParentMapAudit_ok,
    tttLargeFiber36Block4Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block4Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
