import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 4 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block4Chunk0Sources : List Nat :=
  [   1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911,
   1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]

def tttLargeFiber36Row256 : TripleComponentParentRow :=
  tripleRow 1904 272 56 148 148 8 80 80
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

def tttLargeFiber36Row257 : TripleComponentParentRow :=
  tripleRow 1905 273 56 148 149 8 80 81
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

def tttLargeFiber36Row258 : TripleComponentParentRow :=
  tripleRow 1906 274 56 148 150 8 80 82
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

def tttLargeFiber36Row259 : TripleComponentParentRow :=
  tripleRow 1907 1904 56 148 151 56 148 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row260 : TripleComponentParentRow :=
  tripleRow 1908 1904 56 148 164 56 148 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row261 : TripleComponentParentRow :=
  tripleRow 1909 1905 56 148 165 56 148 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row262 : TripleComponentParentRow :=
  tripleRow 1910 278 56 148 166 8 80 102
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

def tttLargeFiber36Row263 : TripleComponentParentRow :=
  tripleRow 1911 279 56 148 167 8 80 103
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

def tttLargeFiber36Row264 : TripleComponentParentRow :=
  tripleRow 1912 280 56 149 156 8 81 88
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

def tttLargeFiber36Row265 : TripleComponentParentRow :=
  tripleRow 1913 281 56 149 157 8 81 89
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

def tttLargeFiber36Row266 : TripleComponentParentRow :=
  tripleRow 1914 282 56 149 158 8 81 90
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

def tttLargeFiber36Row267 : TripleComponentParentRow :=
  tripleRow 1915 1912 56 149 159 56 149 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row268 : TripleComponentParentRow :=
  tripleRow 1916 1912 56 149 172 56 149 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row269 : TripleComponentParentRow :=
  tripleRow 1917 1913 56 149 173 56 149 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row270 : TripleComponentParentRow :=
  tripleRow 1918 286 56 149 174 8 81 110
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

def tttLargeFiber36Row271 : TripleComponentParentRow :=
  tripleRow 1919 287 56 149 175 8 81 111
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

def tttLargeFiber36Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row256
  , tttLargeFiber36Row257
  , tttLargeFiber36Row258
  , tttLargeFiber36Row259
  , tttLargeFiber36Row260
  , tttLargeFiber36Row261
  , tttLargeFiber36Row262
  , tttLargeFiber36Row263
  , tttLargeFiber36Row264
  , tttLargeFiber36Row265
  , tttLargeFiber36Row266
  , tttLargeFiber36Row267
  , tttLargeFiber36Row268
  , tttLargeFiber36Row269
  , tttLargeFiber36Row270
  , tttLargeFiber36Row271
  ]

def tttLargeFiber36Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber36Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber36Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber36Block4Chunk0Sources

theorem tttLargeFiber36Block4Chunk0SourcesCheck_ok :
    tttLargeFiber36Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber36Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block4Chunk0RowValid
    (listGetD tttLargeFiber36Block4Chunk0Rows i default)

def tttLargeFiber36Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block4Chunk0Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block4Chunk0Sources 0 0 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (1 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block4Chunk0Sources 1 0 == 1905
      && tttLargeFiber36ParentOf 1905 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block4Chunk0Sources 2 0 == 1906
      && tttLargeFiber36ParentOf 1906 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block4Chunk0Sources 3 0 == 1907
      && tttLargeFiber36ParentOf 1907 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block4Chunk0Sources 4 0 == 1908
      && tttLargeFiber36ParentOf 1908 == 1904
      && tttLargeFiber36ParentOf 1904 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block4Chunk0Sources 5 0 == 1909
      && tttLargeFiber36ParentOf 1909 == 1905
      && tttLargeFiber36ParentOf 1905 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block4Chunk0Sources 6 0 == 1910
      && tttLargeFiber36ParentOf 1910 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block4Chunk0Sources 7 0 == 1911
      && tttLargeFiber36ParentOf 1911 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block4Chunk0Sources 8 0 == 1912
      && tttLargeFiber36ParentOf 1912 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block4Chunk0Sources 9 0 == 1913
      && tttLargeFiber36ParentOf 1913 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block4Chunk0Sources 10 0 == 1914
      && tttLargeFiber36ParentOf 1914 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block4Chunk0Sources 11 0 == 1915
      && tttLargeFiber36ParentOf 1915 == 1912
      && tttLargeFiber36ParentOf 1912 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block4Chunk0Sources 12 0 == 1916
      && tttLargeFiber36ParentOf 1916 == 1912
      && tttLargeFiber36ParentOf 1912 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block4Chunk0Sources 13 0 == 1917
      && tttLargeFiber36ParentOf 1917 == 1913
      && tttLargeFiber36ParentOf 1913 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block4Chunk0Sources 14 0 == 1918
      && tttLargeFiber36ParentOf 1918 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block4Chunk0Sources 15 0 == 1919
      && tttLargeFiber36ParentOf 1919 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block4Chunk0Row_0_ok :
    tttLargeFiber36Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_1_ok :
    tttLargeFiber36Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_2_ok :
    tttLargeFiber36Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_3_ok :
    tttLargeFiber36Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_4_ok :
    tttLargeFiber36Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_5_ok :
    tttLargeFiber36Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_6_ok :
    tttLargeFiber36Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_7_ok :
    tttLargeFiber36Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_8_ok :
    tttLargeFiber36Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_9_ok :
    tttLargeFiber36Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_10_ok :
    tttLargeFiber36Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_11_ok :
    tttLargeFiber36Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_12_ok :
    tttLargeFiber36Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_13_ok :
    tttLargeFiber36Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_14_ok :
    tttLargeFiber36Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0Row_15_ok :
    tttLargeFiber36Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_0_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_1_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_2_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_3_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_4_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_5_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_6_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_7_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_8_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_9_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_10_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_11_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_12_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_13_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_14_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentMap_15_ok :
    tttLargeFiber36Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_0_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_1_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_2_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_3_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_4_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_5_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_6_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_7_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_8_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_9_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_10_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_11_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_12_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_13_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_14_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block4Chunk0ParentPath_15_ok :
    tttLargeFiber36Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber36Block4Chunk0RowCheck 0
    && tttLargeFiber36Block4Chunk0RowCheck 1
    && tttLargeFiber36Block4Chunk0RowCheck 2
    && tttLargeFiber36Block4Chunk0RowCheck 3
    && tttLargeFiber36Block4Chunk0RowCheck 4
    && tttLargeFiber36Block4Chunk0RowCheck 5
    && tttLargeFiber36Block4Chunk0RowCheck 6
    && tttLargeFiber36Block4Chunk0RowCheck 7
    && tttLargeFiber36Block4Chunk0RowCheck 8
    && tttLargeFiber36Block4Chunk0RowCheck 9
    && tttLargeFiber36Block4Chunk0RowCheck 10
    && tttLargeFiber36Block4Chunk0RowCheck 11
    && tttLargeFiber36Block4Chunk0RowCheck 12
    && tttLargeFiber36Block4Chunk0RowCheck 13
    && tttLargeFiber36Block4Chunk0RowCheck 14
    && tttLargeFiber36Block4Chunk0RowCheck 15

theorem tttLargeFiber36Block4Chunk0RowsAudit_ok :
    tttLargeFiber36Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber36Block4Chunk0RowsAudit,
    tttLargeFiber36Block4Chunk0Row_0_ok,
    tttLargeFiber36Block4Chunk0Row_1_ok,
    tttLargeFiber36Block4Chunk0Row_2_ok,
    tttLargeFiber36Block4Chunk0Row_3_ok,
    tttLargeFiber36Block4Chunk0Row_4_ok,
    tttLargeFiber36Block4Chunk0Row_5_ok,
    tttLargeFiber36Block4Chunk0Row_6_ok,
    tttLargeFiber36Block4Chunk0Row_7_ok,
    tttLargeFiber36Block4Chunk0Row_8_ok,
    tttLargeFiber36Block4Chunk0Row_9_ok,
    tttLargeFiber36Block4Chunk0Row_10_ok,
    tttLargeFiber36Block4Chunk0Row_11_ok,
    tttLargeFiber36Block4Chunk0Row_12_ok,
    tttLargeFiber36Block4Chunk0Row_13_ok,
    tttLargeFiber36Block4Chunk0Row_14_ok,
    tttLargeFiber36Block4Chunk0Row_15_ok]

def tttLargeFiber36Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber36Block4Chunk0ParentMapCheck 0
    && tttLargeFiber36Block4Chunk0ParentMapCheck 1
    && tttLargeFiber36Block4Chunk0ParentMapCheck 2
    && tttLargeFiber36Block4Chunk0ParentMapCheck 3
    && tttLargeFiber36Block4Chunk0ParentMapCheck 4
    && tttLargeFiber36Block4Chunk0ParentMapCheck 5
    && tttLargeFiber36Block4Chunk0ParentMapCheck 6
    && tttLargeFiber36Block4Chunk0ParentMapCheck 7
    && tttLargeFiber36Block4Chunk0ParentMapCheck 8
    && tttLargeFiber36Block4Chunk0ParentMapCheck 9
    && tttLargeFiber36Block4Chunk0ParentMapCheck 10
    && tttLargeFiber36Block4Chunk0ParentMapCheck 11
    && tttLargeFiber36Block4Chunk0ParentMapCheck 12
    && tttLargeFiber36Block4Chunk0ParentMapCheck 13
    && tttLargeFiber36Block4Chunk0ParentMapCheck 14
    && tttLargeFiber36Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber36Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber36Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber36Block4Chunk0ParentMapAudit,
    tttLargeFiber36Block4Chunk0ParentMap_0_ok,
    tttLargeFiber36Block4Chunk0ParentMap_1_ok,
    tttLargeFiber36Block4Chunk0ParentMap_2_ok,
    tttLargeFiber36Block4Chunk0ParentMap_3_ok,
    tttLargeFiber36Block4Chunk0ParentMap_4_ok,
    tttLargeFiber36Block4Chunk0ParentMap_5_ok,
    tttLargeFiber36Block4Chunk0ParentMap_6_ok,
    tttLargeFiber36Block4Chunk0ParentMap_7_ok,
    tttLargeFiber36Block4Chunk0ParentMap_8_ok,
    tttLargeFiber36Block4Chunk0ParentMap_9_ok,
    tttLargeFiber36Block4Chunk0ParentMap_10_ok,
    tttLargeFiber36Block4Chunk0ParentMap_11_ok,
    tttLargeFiber36Block4Chunk0ParentMap_12_ok,
    tttLargeFiber36Block4Chunk0ParentMap_13_ok,
    tttLargeFiber36Block4Chunk0ParentMap_14_ok,
    tttLargeFiber36Block4Chunk0ParentMap_15_ok]

def tttLargeFiber36Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber36Block4Chunk0ParentPathCheck 0
    && tttLargeFiber36Block4Chunk0ParentPathCheck 1
    && tttLargeFiber36Block4Chunk0ParentPathCheck 2
    && tttLargeFiber36Block4Chunk0ParentPathCheck 3
    && tttLargeFiber36Block4Chunk0ParentPathCheck 4
    && tttLargeFiber36Block4Chunk0ParentPathCheck 5
    && tttLargeFiber36Block4Chunk0ParentPathCheck 6
    && tttLargeFiber36Block4Chunk0ParentPathCheck 7
    && tttLargeFiber36Block4Chunk0ParentPathCheck 8
    && tttLargeFiber36Block4Chunk0ParentPathCheck 9
    && tttLargeFiber36Block4Chunk0ParentPathCheck 10
    && tttLargeFiber36Block4Chunk0ParentPathCheck 11
    && tttLargeFiber36Block4Chunk0ParentPathCheck 12
    && tttLargeFiber36Block4Chunk0ParentPathCheck 13
    && tttLargeFiber36Block4Chunk0ParentPathCheck 14
    && tttLargeFiber36Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber36Block4Chunk0ParentsAudit_ok :
    tttLargeFiber36Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber36Block4Chunk0ParentsAudit,
    tttLargeFiber36Block4Chunk0ParentPath_0_ok,
    tttLargeFiber36Block4Chunk0ParentPath_1_ok,
    tttLargeFiber36Block4Chunk0ParentPath_2_ok,
    tttLargeFiber36Block4Chunk0ParentPath_3_ok,
    tttLargeFiber36Block4Chunk0ParentPath_4_ok,
    tttLargeFiber36Block4Chunk0ParentPath_5_ok,
    tttLargeFiber36Block4Chunk0ParentPath_6_ok,
    tttLargeFiber36Block4Chunk0ParentPath_7_ok,
    tttLargeFiber36Block4Chunk0ParentPath_8_ok,
    tttLargeFiber36Block4Chunk0ParentPath_9_ok,
    tttLargeFiber36Block4Chunk0ParentPath_10_ok,
    tttLargeFiber36Block4Chunk0ParentPath_11_ok,
    tttLargeFiber36Block4Chunk0ParentPath_12_ok,
    tttLargeFiber36Block4Chunk0ParentPath_13_ok,
    tttLargeFiber36Block4Chunk0ParentPath_14_ok,
    tttLargeFiber36Block4Chunk0ParentPath_15_ok]

def tttLargeFiber36Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block4Chunk0SourcesCheck &&
    tttLargeFiber36Block4Chunk0RowsAudit &&
    tttLargeFiber36Block4Chunk0ParentMapAudit &&
    tttLargeFiber36Block4Chunk0ParentsAudit

theorem tttLargeFiber36Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber36Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block4Chunk0SourcesCheck_ok,
    tttLargeFiber36Block4Chunk0RowsAudit_ok,
    tttLargeFiber36Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber36Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
