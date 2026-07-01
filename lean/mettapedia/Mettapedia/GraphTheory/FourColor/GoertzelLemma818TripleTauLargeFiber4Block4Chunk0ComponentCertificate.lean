import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 4 chunk 0

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block4Chunk0Sources : List Nat :=
  [3824, 3825, 3826, 3827, 3828, 3829, 3830, 3831,
   3832, 3833, 3834, 3835, 3836, 3837, 3838, 3839]

def tttLargeFiber4Row256 : TripleComponentParentRow :=
  tripleRow 3824 3952 116 132 148 118 64 80
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber4Row257 : TripleComponentParentRow :=
  tripleRow 3825 3953 116 132 149 118 64 81
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber4Row258 : TripleComponentParentRow :=
  tripleRow 3826 3954 116 132 150 118 64 82
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber4Row259 : TripleComponentParentRow :=
  tripleRow 3827 3824 116 132 151 116 132 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row260 : TripleComponentParentRow :=
  tripleRow 3828 3824 116 132 164 116 132 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row261 : TripleComponentParentRow :=
  tripleRow 3829 3825 116 132 165 116 132 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row262 : TripleComponentParentRow :=
  tripleRow 3830 3958 116 132 166 118 64 102
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Row263 : TripleComponentParentRow :=
  tripleRow 3831 3959 116 132 167 118 64 103
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Row264 : TripleComponentParentRow :=
  tripleRow 3832 3960 116 133 156 118 65 88
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber4Row265 : TripleComponentParentRow :=
  tripleRow 3833 3961 116 133 157 118 65 89
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber4Row266 : TripleComponentParentRow :=
  tripleRow 3834 3962 116 133 158 118 65 90
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber4Row267 : TripleComponentParentRow :=
  tripleRow 3835 3832 116 133 159 116 133 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row268 : TripleComponentParentRow :=
  tripleRow 3836 3832 116 133 172 116 133 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row269 : TripleComponentParentRow :=
  tripleRow 3837 3833 116 133 173 116 133 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row270 : TripleComponentParentRow :=
  tripleRow 3838 3966 116 133 174 118 65 110
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Row271 : TripleComponentParentRow :=
  tripleRow 3839 3967 116 133 175 118 65 111
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row256
  , tttLargeFiber4Row257
  , tttLargeFiber4Row258
  , tttLargeFiber4Row259
  , tttLargeFiber4Row260
  , tttLargeFiber4Row261
  , tttLargeFiber4Row262
  , tttLargeFiber4Row263
  , tttLargeFiber4Row264
  , tttLargeFiber4Row265
  , tttLargeFiber4Row266
  , tttLargeFiber4Row267
  , tttLargeFiber4Row268
  , tttLargeFiber4Row269
  , tttLargeFiber4Row270
  , tttLargeFiber4Row271
  ]

def tttLargeFiber4Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber4Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber4Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber4Block4Chunk0Sources

theorem tttLargeFiber4Block4Chunk0SourcesCheck_ok :
    tttLargeFiber4Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber4Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block4Chunk0RowValid
    (listGetD tttLargeFiber4Block4Chunk0Rows i default)

def tttLargeFiber4Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block4Chunk0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block4Chunk0Sources 0 0 == 3824 &&
      tttLargeFiber4ParentOf 3824 == 3952 &&
      tttLargeFiber4ParentOf 3952 == 2240 &&
      tttLargeFiber4ParentOf 2240 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block4Chunk0Sources 1 0 == 3825 &&
      tttLargeFiber4ParentOf 3825 == 3953 &&
      tttLargeFiber4ParentOf 3953 == 2241 &&
      tttLargeFiber4ParentOf 2241 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block4Chunk0Sources 2 0 == 3826 &&
      tttLargeFiber4ParentOf 3826 == 3954 &&
      tttLargeFiber4ParentOf 3954 == 2242 &&
      tttLargeFiber4ParentOf 2242 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block4Chunk0Sources 3 0 == 3827 &&
      tttLargeFiber4ParentOf 3827 == 3824 &&
      tttLargeFiber4ParentOf 3824 == 3952 &&
      tttLargeFiber4ParentOf 3952 == 2240 &&
      tttLargeFiber4ParentOf 2240 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block4Chunk0Sources 4 0 == 3828 &&
      tttLargeFiber4ParentOf 3828 == 3824 &&
      tttLargeFiber4ParentOf 3824 == 3952 &&
      tttLargeFiber4ParentOf 3952 == 2240 &&
      tttLargeFiber4ParentOf 2240 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block4Chunk0Sources 5 0 == 3829 &&
      tttLargeFiber4ParentOf 3829 == 3825 &&
      tttLargeFiber4ParentOf 3825 == 3953 &&
      tttLargeFiber4ParentOf 3953 == 2241 &&
      tttLargeFiber4ParentOf 2241 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block4Chunk0Sources 6 0 == 3830 &&
      tttLargeFiber4ParentOf 3830 == 3958 &&
      tttLargeFiber4ParentOf 3958 == 2246 &&
      tttLargeFiber4ParentOf 2246 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block4Chunk0Sources 7 0 == 3831 &&
      tttLargeFiber4ParentOf 3831 == 3959 &&
      tttLargeFiber4ParentOf 3959 == 2247 &&
      tttLargeFiber4ParentOf 2247 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block4Chunk0Sources 8 0 == 3832 &&
      tttLargeFiber4ParentOf 3832 == 3960 &&
      tttLargeFiber4ParentOf 3960 == 2248 &&
      tttLargeFiber4ParentOf 2248 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block4Chunk0Sources 9 0 == 3833 &&
      tttLargeFiber4ParentOf 3833 == 3961 &&
      tttLargeFiber4ParentOf 3961 == 2249 &&
      tttLargeFiber4ParentOf 2249 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block4Chunk0Sources 10 0 == 3834 &&
      tttLargeFiber4ParentOf 3834 == 3962 &&
      tttLargeFiber4ParentOf 3962 == 2250 &&
      tttLargeFiber4ParentOf 2250 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block4Chunk0Sources 11 0 == 3835 &&
      tttLargeFiber4ParentOf 3835 == 3832 &&
      tttLargeFiber4ParentOf 3832 == 3960 &&
      tttLargeFiber4ParentOf 3960 == 2248 &&
      tttLargeFiber4ParentOf 2248 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block4Chunk0Sources 12 0 == 3836 &&
      tttLargeFiber4ParentOf 3836 == 3832 &&
      tttLargeFiber4ParentOf 3832 == 3960 &&
      tttLargeFiber4ParentOf 3960 == 2248 &&
      tttLargeFiber4ParentOf 2248 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block4Chunk0Sources 13 0 == 3837 &&
      tttLargeFiber4ParentOf 3837 == 3833 &&
      tttLargeFiber4ParentOf 3833 == 3961 &&
      tttLargeFiber4ParentOf 3961 == 2249 &&
      tttLargeFiber4ParentOf 2249 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block4Chunk0Sources 14 0 == 3838 &&
      tttLargeFiber4ParentOf 3838 == 3966 &&
      tttLargeFiber4ParentOf 3966 == 2254 &&
      tttLargeFiber4ParentOf 2254 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block4Chunk0Sources 15 0 == 3839 &&
      tttLargeFiber4ParentOf 3839 == 3967 &&
      tttLargeFiber4ParentOf 3967 == 2255 &&
      tttLargeFiber4ParentOf 2255 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block4Chunk0Row_0_ok :
    tttLargeFiber4Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_1_ok :
    tttLargeFiber4Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_2_ok :
    tttLargeFiber4Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_3_ok :
    tttLargeFiber4Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_4_ok :
    tttLargeFiber4Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_5_ok :
    tttLargeFiber4Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_6_ok :
    tttLargeFiber4Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_7_ok :
    tttLargeFiber4Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_8_ok :
    tttLargeFiber4Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_9_ok :
    tttLargeFiber4Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_10_ok :
    tttLargeFiber4Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_11_ok :
    tttLargeFiber4Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_12_ok :
    tttLargeFiber4Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_13_ok :
    tttLargeFiber4Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_14_ok :
    tttLargeFiber4Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0Row_15_ok :
    tttLargeFiber4Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_0_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_1_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_2_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_3_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_4_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_5_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_6_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_7_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_8_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_9_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_10_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_11_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_12_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_13_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_14_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentMap_15_ok :
    tttLargeFiber4Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_0_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_1_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_2_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_3_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_4_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_5_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_6_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_7_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_8_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_9_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_10_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_11_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_12_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_13_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_14_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk0ParentPath_15_ok :
    tttLargeFiber4Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber4Block4Chunk0RowCheck 0
    && tttLargeFiber4Block4Chunk0RowCheck 1
    && tttLargeFiber4Block4Chunk0RowCheck 2
    && tttLargeFiber4Block4Chunk0RowCheck 3
    && tttLargeFiber4Block4Chunk0RowCheck 4
    && tttLargeFiber4Block4Chunk0RowCheck 5
    && tttLargeFiber4Block4Chunk0RowCheck 6
    && tttLargeFiber4Block4Chunk0RowCheck 7
    && tttLargeFiber4Block4Chunk0RowCheck 8
    && tttLargeFiber4Block4Chunk0RowCheck 9
    && tttLargeFiber4Block4Chunk0RowCheck 10
    && tttLargeFiber4Block4Chunk0RowCheck 11
    && tttLargeFiber4Block4Chunk0RowCheck 12
    && tttLargeFiber4Block4Chunk0RowCheck 13
    && tttLargeFiber4Block4Chunk0RowCheck 14
    && tttLargeFiber4Block4Chunk0RowCheck 15

theorem tttLargeFiber4Block4Chunk0RowsAudit_ok :
    tttLargeFiber4Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber4Block4Chunk0RowsAudit,
    tttLargeFiber4Block4Chunk0Row_0_ok,
    tttLargeFiber4Block4Chunk0Row_1_ok,
    tttLargeFiber4Block4Chunk0Row_2_ok,
    tttLargeFiber4Block4Chunk0Row_3_ok,
    tttLargeFiber4Block4Chunk0Row_4_ok,
    tttLargeFiber4Block4Chunk0Row_5_ok,
    tttLargeFiber4Block4Chunk0Row_6_ok,
    tttLargeFiber4Block4Chunk0Row_7_ok,
    tttLargeFiber4Block4Chunk0Row_8_ok,
    tttLargeFiber4Block4Chunk0Row_9_ok,
    tttLargeFiber4Block4Chunk0Row_10_ok,
    tttLargeFiber4Block4Chunk0Row_11_ok,
    tttLargeFiber4Block4Chunk0Row_12_ok,
    tttLargeFiber4Block4Chunk0Row_13_ok,
    tttLargeFiber4Block4Chunk0Row_14_ok,
    tttLargeFiber4Block4Chunk0Row_15_ok]

def tttLargeFiber4Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber4Block4Chunk0ParentMapCheck 0
    && tttLargeFiber4Block4Chunk0ParentMapCheck 1
    && tttLargeFiber4Block4Chunk0ParentMapCheck 2
    && tttLargeFiber4Block4Chunk0ParentMapCheck 3
    && tttLargeFiber4Block4Chunk0ParentMapCheck 4
    && tttLargeFiber4Block4Chunk0ParentMapCheck 5
    && tttLargeFiber4Block4Chunk0ParentMapCheck 6
    && tttLargeFiber4Block4Chunk0ParentMapCheck 7
    && tttLargeFiber4Block4Chunk0ParentMapCheck 8
    && tttLargeFiber4Block4Chunk0ParentMapCheck 9
    && tttLargeFiber4Block4Chunk0ParentMapCheck 10
    && tttLargeFiber4Block4Chunk0ParentMapCheck 11
    && tttLargeFiber4Block4Chunk0ParentMapCheck 12
    && tttLargeFiber4Block4Chunk0ParentMapCheck 13
    && tttLargeFiber4Block4Chunk0ParentMapCheck 14
    && tttLargeFiber4Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber4Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber4Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber4Block4Chunk0ParentMapAudit,
    tttLargeFiber4Block4Chunk0ParentMap_0_ok,
    tttLargeFiber4Block4Chunk0ParentMap_1_ok,
    tttLargeFiber4Block4Chunk0ParentMap_2_ok,
    tttLargeFiber4Block4Chunk0ParentMap_3_ok,
    tttLargeFiber4Block4Chunk0ParentMap_4_ok,
    tttLargeFiber4Block4Chunk0ParentMap_5_ok,
    tttLargeFiber4Block4Chunk0ParentMap_6_ok,
    tttLargeFiber4Block4Chunk0ParentMap_7_ok,
    tttLargeFiber4Block4Chunk0ParentMap_8_ok,
    tttLargeFiber4Block4Chunk0ParentMap_9_ok,
    tttLargeFiber4Block4Chunk0ParentMap_10_ok,
    tttLargeFiber4Block4Chunk0ParentMap_11_ok,
    tttLargeFiber4Block4Chunk0ParentMap_12_ok,
    tttLargeFiber4Block4Chunk0ParentMap_13_ok,
    tttLargeFiber4Block4Chunk0ParentMap_14_ok,
    tttLargeFiber4Block4Chunk0ParentMap_15_ok]

def tttLargeFiber4Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber4Block4Chunk0ParentPathCheck 0
    && tttLargeFiber4Block4Chunk0ParentPathCheck 1
    && tttLargeFiber4Block4Chunk0ParentPathCheck 2
    && tttLargeFiber4Block4Chunk0ParentPathCheck 3
    && tttLargeFiber4Block4Chunk0ParentPathCheck 4
    && tttLargeFiber4Block4Chunk0ParentPathCheck 5
    && tttLargeFiber4Block4Chunk0ParentPathCheck 6
    && tttLargeFiber4Block4Chunk0ParentPathCheck 7
    && tttLargeFiber4Block4Chunk0ParentPathCheck 8
    && tttLargeFiber4Block4Chunk0ParentPathCheck 9
    && tttLargeFiber4Block4Chunk0ParentPathCheck 10
    && tttLargeFiber4Block4Chunk0ParentPathCheck 11
    && tttLargeFiber4Block4Chunk0ParentPathCheck 12
    && tttLargeFiber4Block4Chunk0ParentPathCheck 13
    && tttLargeFiber4Block4Chunk0ParentPathCheck 14
    && tttLargeFiber4Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber4Block4Chunk0ParentsAudit_ok :
    tttLargeFiber4Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber4Block4Chunk0ParentsAudit,
    tttLargeFiber4Block4Chunk0ParentPath_0_ok,
    tttLargeFiber4Block4Chunk0ParentPath_1_ok,
    tttLargeFiber4Block4Chunk0ParentPath_2_ok,
    tttLargeFiber4Block4Chunk0ParentPath_3_ok,
    tttLargeFiber4Block4Chunk0ParentPath_4_ok,
    tttLargeFiber4Block4Chunk0ParentPath_5_ok,
    tttLargeFiber4Block4Chunk0ParentPath_6_ok,
    tttLargeFiber4Block4Chunk0ParentPath_7_ok,
    tttLargeFiber4Block4Chunk0ParentPath_8_ok,
    tttLargeFiber4Block4Chunk0ParentPath_9_ok,
    tttLargeFiber4Block4Chunk0ParentPath_10_ok,
    tttLargeFiber4Block4Chunk0ParentPath_11_ok,
    tttLargeFiber4Block4Chunk0ParentPath_12_ok,
    tttLargeFiber4Block4Chunk0ParentPath_13_ok,
    tttLargeFiber4Block4Chunk0ParentPath_14_ok,
    tttLargeFiber4Block4Chunk0ParentPath_15_ok]

def tttLargeFiber4Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block4Chunk0SourcesCheck &&
    tttLargeFiber4Block4Chunk0RowsAudit &&
    tttLargeFiber4Block4Chunk0ParentMapAudit &&
    tttLargeFiber4Block4Chunk0ParentsAudit

theorem tttLargeFiber4Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber4Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block4Chunk0SourcesCheck_ok,
    tttLargeFiber4Block4Chunk0RowsAudit_ok,
    tttLargeFiber4Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber4Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
