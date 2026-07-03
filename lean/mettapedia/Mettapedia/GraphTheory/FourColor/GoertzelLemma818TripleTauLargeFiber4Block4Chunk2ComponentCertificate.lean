import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 4 chunk 2

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block4Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block4Chunk2Sources : List Nat :=
  [3856, 3857, 3858, 3859, 3860, 3861, 3862, 3863,
   3864, 3865, 3866, 3867, 3868, 3869, 3870, 3871]

def tttLargeFiber4Row288 : TripleComponentParentRow :=
  tripleRow 3856 3872 116 180 132 116 182 64
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

def tttLargeFiber4Row289 : TripleComponentParentRow :=
  tripleRow 3857 3873 116 180 133 116 182 65
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

def tttLargeFiber4Row290 : TripleComponentParentRow :=
  tripleRow 3858 2326 116 180 134 66 18 34
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber4Row291 : TripleComponentParentRow :=
  tripleRow 3859 2327 116 180 135 66 18 35
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber4Row292 : TripleComponentParentRow :=
  tripleRow 3860 2322 116 180 180 66 18 18
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber4Row293 : TripleComponentParentRow :=
  tripleRow 3861 3863 116 180 181 116 180 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row294 : TripleComponentParentRow :=
  tripleRow 3862 2321 116 180 182 66 18 17
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row295 : TripleComponentParentRow :=
  tripleRow 3863 2320 116 180 183 66 18 16
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber4Row296 : TripleComponentParentRow :=
  tripleRow 3864 3880 116 181 140 116 183 72
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

def tttLargeFiber4Row297 : TripleComponentParentRow :=
  tripleRow 3865 3881 116 181 141 116 183 73
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

def tttLargeFiber4Row298 : TripleComponentParentRow :=
  tripleRow 3866 3882 116 181 142 116 183 74
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

def tttLargeFiber4Row299 : TripleComponentParentRow :=
  tripleRow 3867 3864 116 181 143 116 181 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row300 : TripleComponentParentRow :=
  tripleRow 3868 3864 116 181 188 116 181 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row301 : TripleComponentParentRow :=
  tripleRow 3869 3865 116 181 189 116 181 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row302 : TripleComponentParentRow :=
  tripleRow 3870 3886 116 181 190 116 183 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row303 : TripleComponentParentRow :=
  tripleRow 3871 3887 116 181 191 116 183 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Block4Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row288
  , tttLargeFiber4Row289
  , tttLargeFiber4Row290
  , tttLargeFiber4Row291
  , tttLargeFiber4Row292
  , tttLargeFiber4Row293
  , tttLargeFiber4Row294
  , tttLargeFiber4Row295
  , tttLargeFiber4Row296
  , tttLargeFiber4Row297
  , tttLargeFiber4Row298
  , tttLargeFiber4Row299
  , tttLargeFiber4Row300
  , tttLargeFiber4Row301
  , tttLargeFiber4Row302
  , tttLargeFiber4Row303
  ]

def tttLargeFiber4Block4Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block4Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block4Chunk2ExpectedContains row.source &&
    tttLargeFiber4Block4Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block4Chunk2SourcesCheck : Bool :=
  (tttLargeFiber4Block4Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber4Block4Chunk2Sources

theorem tttLargeFiber4Block4Chunk2SourcesCheck_ok :
    tttLargeFiber4Block4Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber4Block4Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block4Chunk2RowValid
    (listGetD tttLargeFiber4Block4Chunk2Rows i default)

def tttLargeFiber4Block4Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block4Chunk2Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block4Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block4Chunk2Sources 0 0 == 3856 &&
      tttLargeFiber4ParentOf 3856 == 3872 &&
      tttLargeFiber4ParentOf 3872 == 2312 &&
      tttLargeFiber4ParentOf 2312 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block4Chunk2Sources 1 0 == 3857 &&
      tttLargeFiber4ParentOf 3857 == 3873 &&
      tttLargeFiber4ParentOf 3873 == 2313 &&
      tttLargeFiber4ParentOf 2313 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block4Chunk2Sources 2 0 == 3858 &&
      tttLargeFiber4ParentOf 3858 == 2326 &&
      tttLargeFiber4ParentOf 2326 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block4Chunk2Sources 3 0 == 3859 &&
      tttLargeFiber4ParentOf 3859 == 2327 &&
      tttLargeFiber4ParentOf 2327 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block4Chunk2Sources 4 0 == 3860 &&
      tttLargeFiber4ParentOf 3860 == 2322 &&
      tttLargeFiber4ParentOf 2322 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block4Chunk2Sources 5 0 == 3861 &&
      tttLargeFiber4ParentOf 3861 == 3863 &&
      tttLargeFiber4ParentOf 3863 == 2320 &&
      tttLargeFiber4ParentOf 2320 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block4Chunk2Sources 6 0 == 3862 &&
      tttLargeFiber4ParentOf 3862 == 2321 &&
      tttLargeFiber4ParentOf 2321 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block4Chunk2Sources 7 0 == 3863 &&
      tttLargeFiber4ParentOf 3863 == 2320 &&
      tttLargeFiber4ParentOf 2320 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block4Chunk2Sources 8 0 == 3864 &&
      tttLargeFiber4ParentOf 3864 == 3880 &&
      tttLargeFiber4ParentOf 3880 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block4Chunk2Sources 9 0 == 3865 &&
      tttLargeFiber4ParentOf 3865 == 3881 &&
      tttLargeFiber4ParentOf 3881 == 2305 &&
      tttLargeFiber4ParentOf 2305 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block4Chunk2Sources 10 0 == 3866 &&
      tttLargeFiber4ParentOf 3866 == 3882 &&
      tttLargeFiber4ParentOf 3882 == 2306 &&
      tttLargeFiber4ParentOf 2306 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block4Chunk2Sources 11 0 == 3867 &&
      tttLargeFiber4ParentOf 3867 == 3864 &&
      tttLargeFiber4ParentOf 3864 == 3880 &&
      tttLargeFiber4ParentOf 3880 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block4Chunk2Sources 12 0 == 3868 &&
      tttLargeFiber4ParentOf 3868 == 3864 &&
      tttLargeFiber4ParentOf 3864 == 3880 &&
      tttLargeFiber4ParentOf 3880 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block4Chunk2Sources 13 0 == 3869 &&
      tttLargeFiber4ParentOf 3869 == 3865 &&
      tttLargeFiber4ParentOf 3865 == 3881 &&
      tttLargeFiber4ParentOf 3881 == 2305 &&
      tttLargeFiber4ParentOf 2305 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block4Chunk2Sources 14 0 == 3870 &&
      tttLargeFiber4ParentOf 3870 == 3886 &&
      tttLargeFiber4ParentOf 3886 == 2310 &&
      tttLargeFiber4ParentOf 2310 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block4Chunk2Sources 15 0 == 3871 &&
      tttLargeFiber4ParentOf 3871 == 3887 &&
      tttLargeFiber4ParentOf 3887 == 2311 &&
      tttLargeFiber4ParentOf 2311 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block4Chunk2Row_0_ok :
    tttLargeFiber4Block4Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_1_ok :
    tttLargeFiber4Block4Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_2_ok :
    tttLargeFiber4Block4Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_3_ok :
    tttLargeFiber4Block4Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_4_ok :
    tttLargeFiber4Block4Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_5_ok :
    tttLargeFiber4Block4Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_6_ok :
    tttLargeFiber4Block4Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_7_ok :
    tttLargeFiber4Block4Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_8_ok :
    tttLargeFiber4Block4Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_9_ok :
    tttLargeFiber4Block4Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_10_ok :
    tttLargeFiber4Block4Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_11_ok :
    tttLargeFiber4Block4Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_12_ok :
    tttLargeFiber4Block4Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_13_ok :
    tttLargeFiber4Block4Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_14_ok :
    tttLargeFiber4Block4Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2Row_15_ok :
    tttLargeFiber4Block4Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_0_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_1_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_2_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_3_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_4_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_5_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_6_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_7_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_8_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_9_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_10_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_11_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_12_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_13_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_14_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentMap_15_ok :
    tttLargeFiber4Block4Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_0_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_1_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_2_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_3_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_4_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_5_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_6_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_7_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_8_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_9_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_10_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_11_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_12_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_13_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_14_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk2ParentPath_15_ok :
    tttLargeFiber4Block4Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block4Chunk2RowsAudit : Bool :=
  tttLargeFiber4Block4Chunk2RowCheck 0
    && tttLargeFiber4Block4Chunk2RowCheck 1
    && tttLargeFiber4Block4Chunk2RowCheck 2
    && tttLargeFiber4Block4Chunk2RowCheck 3
    && tttLargeFiber4Block4Chunk2RowCheck 4
    && tttLargeFiber4Block4Chunk2RowCheck 5
    && tttLargeFiber4Block4Chunk2RowCheck 6
    && tttLargeFiber4Block4Chunk2RowCheck 7
    && tttLargeFiber4Block4Chunk2RowCheck 8
    && tttLargeFiber4Block4Chunk2RowCheck 9
    && tttLargeFiber4Block4Chunk2RowCheck 10
    && tttLargeFiber4Block4Chunk2RowCheck 11
    && tttLargeFiber4Block4Chunk2RowCheck 12
    && tttLargeFiber4Block4Chunk2RowCheck 13
    && tttLargeFiber4Block4Chunk2RowCheck 14
    && tttLargeFiber4Block4Chunk2RowCheck 15

theorem tttLargeFiber4Block4Chunk2RowsAudit_ok :
    tttLargeFiber4Block4Chunk2RowsAudit = true := by
  simp [tttLargeFiber4Block4Chunk2RowsAudit,
    tttLargeFiber4Block4Chunk2Row_0_ok,
    tttLargeFiber4Block4Chunk2Row_1_ok,
    tttLargeFiber4Block4Chunk2Row_2_ok,
    tttLargeFiber4Block4Chunk2Row_3_ok,
    tttLargeFiber4Block4Chunk2Row_4_ok,
    tttLargeFiber4Block4Chunk2Row_5_ok,
    tttLargeFiber4Block4Chunk2Row_6_ok,
    tttLargeFiber4Block4Chunk2Row_7_ok,
    tttLargeFiber4Block4Chunk2Row_8_ok,
    tttLargeFiber4Block4Chunk2Row_9_ok,
    tttLargeFiber4Block4Chunk2Row_10_ok,
    tttLargeFiber4Block4Chunk2Row_11_ok,
    tttLargeFiber4Block4Chunk2Row_12_ok,
    tttLargeFiber4Block4Chunk2Row_13_ok,
    tttLargeFiber4Block4Chunk2Row_14_ok,
    tttLargeFiber4Block4Chunk2Row_15_ok]

def tttLargeFiber4Block4Chunk2ParentMapAudit : Bool :=
  tttLargeFiber4Block4Chunk2ParentMapCheck 0
    && tttLargeFiber4Block4Chunk2ParentMapCheck 1
    && tttLargeFiber4Block4Chunk2ParentMapCheck 2
    && tttLargeFiber4Block4Chunk2ParentMapCheck 3
    && tttLargeFiber4Block4Chunk2ParentMapCheck 4
    && tttLargeFiber4Block4Chunk2ParentMapCheck 5
    && tttLargeFiber4Block4Chunk2ParentMapCheck 6
    && tttLargeFiber4Block4Chunk2ParentMapCheck 7
    && tttLargeFiber4Block4Chunk2ParentMapCheck 8
    && tttLargeFiber4Block4Chunk2ParentMapCheck 9
    && tttLargeFiber4Block4Chunk2ParentMapCheck 10
    && tttLargeFiber4Block4Chunk2ParentMapCheck 11
    && tttLargeFiber4Block4Chunk2ParentMapCheck 12
    && tttLargeFiber4Block4Chunk2ParentMapCheck 13
    && tttLargeFiber4Block4Chunk2ParentMapCheck 14
    && tttLargeFiber4Block4Chunk2ParentMapCheck 15

theorem tttLargeFiber4Block4Chunk2ParentMapAudit_ok :
    tttLargeFiber4Block4Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber4Block4Chunk2ParentMapAudit,
    tttLargeFiber4Block4Chunk2ParentMap_0_ok,
    tttLargeFiber4Block4Chunk2ParentMap_1_ok,
    tttLargeFiber4Block4Chunk2ParentMap_2_ok,
    tttLargeFiber4Block4Chunk2ParentMap_3_ok,
    tttLargeFiber4Block4Chunk2ParentMap_4_ok,
    tttLargeFiber4Block4Chunk2ParentMap_5_ok,
    tttLargeFiber4Block4Chunk2ParentMap_6_ok,
    tttLargeFiber4Block4Chunk2ParentMap_7_ok,
    tttLargeFiber4Block4Chunk2ParentMap_8_ok,
    tttLargeFiber4Block4Chunk2ParentMap_9_ok,
    tttLargeFiber4Block4Chunk2ParentMap_10_ok,
    tttLargeFiber4Block4Chunk2ParentMap_11_ok,
    tttLargeFiber4Block4Chunk2ParentMap_12_ok,
    tttLargeFiber4Block4Chunk2ParentMap_13_ok,
    tttLargeFiber4Block4Chunk2ParentMap_14_ok,
    tttLargeFiber4Block4Chunk2ParentMap_15_ok]

def tttLargeFiber4Block4Chunk2ParentsAudit : Bool :=
  tttLargeFiber4Block4Chunk2ParentPathCheck 0
    && tttLargeFiber4Block4Chunk2ParentPathCheck 1
    && tttLargeFiber4Block4Chunk2ParentPathCheck 2
    && tttLargeFiber4Block4Chunk2ParentPathCheck 3
    && tttLargeFiber4Block4Chunk2ParentPathCheck 4
    && tttLargeFiber4Block4Chunk2ParentPathCheck 5
    && tttLargeFiber4Block4Chunk2ParentPathCheck 6
    && tttLargeFiber4Block4Chunk2ParentPathCheck 7
    && tttLargeFiber4Block4Chunk2ParentPathCheck 8
    && tttLargeFiber4Block4Chunk2ParentPathCheck 9
    && tttLargeFiber4Block4Chunk2ParentPathCheck 10
    && tttLargeFiber4Block4Chunk2ParentPathCheck 11
    && tttLargeFiber4Block4Chunk2ParentPathCheck 12
    && tttLargeFiber4Block4Chunk2ParentPathCheck 13
    && tttLargeFiber4Block4Chunk2ParentPathCheck 14
    && tttLargeFiber4Block4Chunk2ParentPathCheck 15

theorem tttLargeFiber4Block4Chunk2ParentsAudit_ok :
    tttLargeFiber4Block4Chunk2ParentsAudit = true := by
  simp [tttLargeFiber4Block4Chunk2ParentsAudit,
    tttLargeFiber4Block4Chunk2ParentPath_0_ok,
    tttLargeFiber4Block4Chunk2ParentPath_1_ok,
    tttLargeFiber4Block4Chunk2ParentPath_2_ok,
    tttLargeFiber4Block4Chunk2ParentPath_3_ok,
    tttLargeFiber4Block4Chunk2ParentPath_4_ok,
    tttLargeFiber4Block4Chunk2ParentPath_5_ok,
    tttLargeFiber4Block4Chunk2ParentPath_6_ok,
    tttLargeFiber4Block4Chunk2ParentPath_7_ok,
    tttLargeFiber4Block4Chunk2ParentPath_8_ok,
    tttLargeFiber4Block4Chunk2ParentPath_9_ok,
    tttLargeFiber4Block4Chunk2ParentPath_10_ok,
    tttLargeFiber4Block4Chunk2ParentPath_11_ok,
    tttLargeFiber4Block4Chunk2ParentPath_12_ok,
    tttLargeFiber4Block4Chunk2ParentPath_13_ok,
    tttLargeFiber4Block4Chunk2ParentPath_14_ok,
    tttLargeFiber4Block4Chunk2ParentPath_15_ok]

def tttLargeFiber4Block4Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block4Chunk2SourcesCheck &&
    tttLargeFiber4Block4Chunk2RowsAudit &&
    tttLargeFiber4Block4Chunk2ParentMapAudit &&
    tttLargeFiber4Block4Chunk2ParentsAudit

theorem tttLargeFiber4Block4Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber4Block4Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block4Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block4Chunk2SourcesCheck_ok,
    tttLargeFiber4Block4Chunk2RowsAudit_ok,
    tttLargeFiber4Block4Chunk2ParentMapAudit_ok,
    tttLargeFiber4Block4Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block4Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
