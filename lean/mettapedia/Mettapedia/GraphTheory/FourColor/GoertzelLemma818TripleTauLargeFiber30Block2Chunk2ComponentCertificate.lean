import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 2 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block2Chunk2Sources : List Nat :=
  [   160, 161, 162, 163, 164, 165, 166, 167,
   168, 169, 170, 171, 172, 173, 174, 175]

def tttLargeFiber30Row160 : TripleComponentParentRow :=
  tripleRow 160 128 2 32 148 2 16 80
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row161 : TripleComponentParentRow :=
  tripleRow 161 129 2 32 149 2 16 81
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row162 : TripleComponentParentRow :=
  tripleRow 162 130 2 32 150 2 16 82
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber30Row163 : TripleComponentParentRow :=
  tripleRow 163 160 2 32 151 2 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row164 : TripleComponentParentRow :=
  tripleRow 164 160 2 32 164 2 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row165 : TripleComponentParentRow :=
  tripleRow 165 161 2 32 165 2 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row166 : TripleComponentParentRow :=
  tripleRow 166 134 2 32 166 2 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row167 : TripleComponentParentRow :=
  tripleRow 167 135 2 32 167 2 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row168 : TripleComponentParentRow :=
  tripleRow 168 136 2 33 156 2 17 88
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row169 : TripleComponentParentRow :=
  tripleRow 169 137 2 33 157 2 17 89
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row170 : TripleComponentParentRow :=
  tripleRow 170 138 2 33 158 2 17 90
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber30Row171 : TripleComponentParentRow :=
  tripleRow 171 168 2 33 159 2 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row172 : TripleComponentParentRow :=
  tripleRow 172 168 2 33 172 2 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row173 : TripleComponentParentRow :=
  tripleRow 173 169 2 33 173 2 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row174 : TripleComponentParentRow :=
  tripleRow 174 142 2 33 174 2 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row175 : TripleComponentParentRow :=
  tripleRow 175 143 2 33 175 2 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row160
  , tttLargeFiber30Row161
  , tttLargeFiber30Row162
  , tttLargeFiber30Row163
  , tttLargeFiber30Row164
  , tttLargeFiber30Row165
  , tttLargeFiber30Row166
  , tttLargeFiber30Row167
  , tttLargeFiber30Row168
  , tttLargeFiber30Row169
  , tttLargeFiber30Row170
  , tttLargeFiber30Row171
  , tttLargeFiber30Row172
  , tttLargeFiber30Row173
  , tttLargeFiber30Row174
  , tttLargeFiber30Row175
  ]

def tttLargeFiber30Block2Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block2Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block2Chunk2ExpectedContains row.source &&
    tttLargeFiber30Block2Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber30Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber30Block2Chunk2Sources

theorem tttLargeFiber30Block2Chunk2SourcesCheck_ok :
    tttLargeFiber30Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber30Block2Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block2Chunk2RowValid
    (listGetD tttLargeFiber30Block2Chunk2Rows i default)

def tttLargeFiber30Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block2Chunk2Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block2Chunk2Sources 0 0 == 160
      && tttLargeFiber30ParentOf 160 == 128
      && tttLargeFiber30ParentOf 128 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block2Chunk2Sources 1 0 == 161
      && tttLargeFiber30ParentOf 161 == 129
      && tttLargeFiber30ParentOf 129 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block2Chunk2Sources 2 0 == 162
      && tttLargeFiber30ParentOf 162 == 130
      && tttLargeFiber30ParentOf 130 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block2Chunk2Sources 3 0 == 163
      && tttLargeFiber30ParentOf 163 == 160
      && tttLargeFiber30ParentOf 160 == 128
      && tttLargeFiber30ParentOf 128 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block2Chunk2Sources 4 0 == 164
      && tttLargeFiber30ParentOf 164 == 160
      && tttLargeFiber30ParentOf 160 == 128
      && tttLargeFiber30ParentOf 128 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block2Chunk2Sources 5 0 == 165
      && tttLargeFiber30ParentOf 165 == 161
      && tttLargeFiber30ParentOf 161 == 129
      && tttLargeFiber30ParentOf 129 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block2Chunk2Sources 6 0 == 166
      && tttLargeFiber30ParentOf 166 == 134
      && tttLargeFiber30ParentOf 134 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block2Chunk2Sources 7 0 == 167
      && tttLargeFiber30ParentOf 167 == 135
      && tttLargeFiber30ParentOf 135 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block2Chunk2Sources 8 0 == 168
      && tttLargeFiber30ParentOf 168 == 136
      && tttLargeFiber30ParentOf 136 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block2Chunk2Sources 9 0 == 169
      && tttLargeFiber30ParentOf 169 == 137
      && tttLargeFiber30ParentOf 137 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block2Chunk2Sources 10 0 == 170
      && tttLargeFiber30ParentOf 170 == 138
      && tttLargeFiber30ParentOf 138 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block2Chunk2Sources 11 0 == 171
      && tttLargeFiber30ParentOf 171 == 168
      && tttLargeFiber30ParentOf 168 == 136
      && tttLargeFiber30ParentOf 136 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block2Chunk2Sources 12 0 == 172
      && tttLargeFiber30ParentOf 172 == 168
      && tttLargeFiber30ParentOf 168 == 136
      && tttLargeFiber30ParentOf 136 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block2Chunk2Sources 13 0 == 173
      && tttLargeFiber30ParentOf 173 == 169
      && tttLargeFiber30ParentOf 169 == 137
      && tttLargeFiber30ParentOf 137 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block2Chunk2Sources 14 0 == 174
      && tttLargeFiber30ParentOf 174 == 142
      && tttLargeFiber30ParentOf 142 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block2Chunk2Sources 15 0 == 175
      && tttLargeFiber30ParentOf 175 == 143
      && tttLargeFiber30ParentOf 143 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block2Chunk2Row_0_ok :
    tttLargeFiber30Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_1_ok :
    tttLargeFiber30Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_2_ok :
    tttLargeFiber30Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_3_ok :
    tttLargeFiber30Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_4_ok :
    tttLargeFiber30Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_5_ok :
    tttLargeFiber30Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_6_ok :
    tttLargeFiber30Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_7_ok :
    tttLargeFiber30Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_8_ok :
    tttLargeFiber30Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_9_ok :
    tttLargeFiber30Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_10_ok :
    tttLargeFiber30Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_11_ok :
    tttLargeFiber30Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_12_ok :
    tttLargeFiber30Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_13_ok :
    tttLargeFiber30Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_14_ok :
    tttLargeFiber30Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2Row_15_ok :
    tttLargeFiber30Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_0_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_1_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_2_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_3_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_4_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_5_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_6_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_7_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_8_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_9_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_10_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_11_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_12_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_13_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_14_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentMap_15_ok :
    tttLargeFiber30Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_0_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_1_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_2_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_3_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_4_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_5_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_6_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_7_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_8_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_9_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_10_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_11_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_12_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_13_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_14_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk2ParentPath_15_ok :
    tttLargeFiber30Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber30Block2Chunk2RowCheck 0
    && tttLargeFiber30Block2Chunk2RowCheck 1
    && tttLargeFiber30Block2Chunk2RowCheck 2
    && tttLargeFiber30Block2Chunk2RowCheck 3
    && tttLargeFiber30Block2Chunk2RowCheck 4
    && tttLargeFiber30Block2Chunk2RowCheck 5
    && tttLargeFiber30Block2Chunk2RowCheck 6
    && tttLargeFiber30Block2Chunk2RowCheck 7
    && tttLargeFiber30Block2Chunk2RowCheck 8
    && tttLargeFiber30Block2Chunk2RowCheck 9
    && tttLargeFiber30Block2Chunk2RowCheck 10
    && tttLargeFiber30Block2Chunk2RowCheck 11
    && tttLargeFiber30Block2Chunk2RowCheck 12
    && tttLargeFiber30Block2Chunk2RowCheck 13
    && tttLargeFiber30Block2Chunk2RowCheck 14
    && tttLargeFiber30Block2Chunk2RowCheck 15

theorem tttLargeFiber30Block2Chunk2RowsAudit_ok :
    tttLargeFiber30Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber30Block2Chunk2RowsAudit,
    tttLargeFiber30Block2Chunk2Row_0_ok,
    tttLargeFiber30Block2Chunk2Row_1_ok,
    tttLargeFiber30Block2Chunk2Row_2_ok,
    tttLargeFiber30Block2Chunk2Row_3_ok,
    tttLargeFiber30Block2Chunk2Row_4_ok,
    tttLargeFiber30Block2Chunk2Row_5_ok,
    tttLargeFiber30Block2Chunk2Row_6_ok,
    tttLargeFiber30Block2Chunk2Row_7_ok,
    tttLargeFiber30Block2Chunk2Row_8_ok,
    tttLargeFiber30Block2Chunk2Row_9_ok,
    tttLargeFiber30Block2Chunk2Row_10_ok,
    tttLargeFiber30Block2Chunk2Row_11_ok,
    tttLargeFiber30Block2Chunk2Row_12_ok,
    tttLargeFiber30Block2Chunk2Row_13_ok,
    tttLargeFiber30Block2Chunk2Row_14_ok,
    tttLargeFiber30Block2Chunk2Row_15_ok]

def tttLargeFiber30Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber30Block2Chunk2ParentMapCheck 0
    && tttLargeFiber30Block2Chunk2ParentMapCheck 1
    && tttLargeFiber30Block2Chunk2ParentMapCheck 2
    && tttLargeFiber30Block2Chunk2ParentMapCheck 3
    && tttLargeFiber30Block2Chunk2ParentMapCheck 4
    && tttLargeFiber30Block2Chunk2ParentMapCheck 5
    && tttLargeFiber30Block2Chunk2ParentMapCheck 6
    && tttLargeFiber30Block2Chunk2ParentMapCheck 7
    && tttLargeFiber30Block2Chunk2ParentMapCheck 8
    && tttLargeFiber30Block2Chunk2ParentMapCheck 9
    && tttLargeFiber30Block2Chunk2ParentMapCheck 10
    && tttLargeFiber30Block2Chunk2ParentMapCheck 11
    && tttLargeFiber30Block2Chunk2ParentMapCheck 12
    && tttLargeFiber30Block2Chunk2ParentMapCheck 13
    && tttLargeFiber30Block2Chunk2ParentMapCheck 14
    && tttLargeFiber30Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber30Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber30Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber30Block2Chunk2ParentMapAudit,
    tttLargeFiber30Block2Chunk2ParentMap_0_ok,
    tttLargeFiber30Block2Chunk2ParentMap_1_ok,
    tttLargeFiber30Block2Chunk2ParentMap_2_ok,
    tttLargeFiber30Block2Chunk2ParentMap_3_ok,
    tttLargeFiber30Block2Chunk2ParentMap_4_ok,
    tttLargeFiber30Block2Chunk2ParentMap_5_ok,
    tttLargeFiber30Block2Chunk2ParentMap_6_ok,
    tttLargeFiber30Block2Chunk2ParentMap_7_ok,
    tttLargeFiber30Block2Chunk2ParentMap_8_ok,
    tttLargeFiber30Block2Chunk2ParentMap_9_ok,
    tttLargeFiber30Block2Chunk2ParentMap_10_ok,
    tttLargeFiber30Block2Chunk2ParentMap_11_ok,
    tttLargeFiber30Block2Chunk2ParentMap_12_ok,
    tttLargeFiber30Block2Chunk2ParentMap_13_ok,
    tttLargeFiber30Block2Chunk2ParentMap_14_ok,
    tttLargeFiber30Block2Chunk2ParentMap_15_ok]

def tttLargeFiber30Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber30Block2Chunk2ParentPathCheck 0
    && tttLargeFiber30Block2Chunk2ParentPathCheck 1
    && tttLargeFiber30Block2Chunk2ParentPathCheck 2
    && tttLargeFiber30Block2Chunk2ParentPathCheck 3
    && tttLargeFiber30Block2Chunk2ParentPathCheck 4
    && tttLargeFiber30Block2Chunk2ParentPathCheck 5
    && tttLargeFiber30Block2Chunk2ParentPathCheck 6
    && tttLargeFiber30Block2Chunk2ParentPathCheck 7
    && tttLargeFiber30Block2Chunk2ParentPathCheck 8
    && tttLargeFiber30Block2Chunk2ParentPathCheck 9
    && tttLargeFiber30Block2Chunk2ParentPathCheck 10
    && tttLargeFiber30Block2Chunk2ParentPathCheck 11
    && tttLargeFiber30Block2Chunk2ParentPathCheck 12
    && tttLargeFiber30Block2Chunk2ParentPathCheck 13
    && tttLargeFiber30Block2Chunk2ParentPathCheck 14
    && tttLargeFiber30Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber30Block2Chunk2ParentsAudit_ok :
    tttLargeFiber30Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber30Block2Chunk2ParentsAudit,
    tttLargeFiber30Block2Chunk2ParentPath_0_ok,
    tttLargeFiber30Block2Chunk2ParentPath_1_ok,
    tttLargeFiber30Block2Chunk2ParentPath_2_ok,
    tttLargeFiber30Block2Chunk2ParentPath_3_ok,
    tttLargeFiber30Block2Chunk2ParentPath_4_ok,
    tttLargeFiber30Block2Chunk2ParentPath_5_ok,
    tttLargeFiber30Block2Chunk2ParentPath_6_ok,
    tttLargeFiber30Block2Chunk2ParentPath_7_ok,
    tttLargeFiber30Block2Chunk2ParentPath_8_ok,
    tttLargeFiber30Block2Chunk2ParentPath_9_ok,
    tttLargeFiber30Block2Chunk2ParentPath_10_ok,
    tttLargeFiber30Block2Chunk2ParentPath_11_ok,
    tttLargeFiber30Block2Chunk2ParentPath_12_ok,
    tttLargeFiber30Block2Chunk2ParentPath_13_ok,
    tttLargeFiber30Block2Chunk2ParentPath_14_ok,
    tttLargeFiber30Block2Chunk2ParentPath_15_ok]

def tttLargeFiber30Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block2Chunk2SourcesCheck &&
    tttLargeFiber30Block2Chunk2RowsAudit &&
    tttLargeFiber30Block2Chunk2ParentMapAudit &&
    tttLargeFiber30Block2Chunk2ParentsAudit

theorem tttLargeFiber30Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber30Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block2Chunk2SourcesCheck_ok,
    tttLargeFiber30Block2Chunk2RowsAudit_ok,
    tttLargeFiber30Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber30Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
