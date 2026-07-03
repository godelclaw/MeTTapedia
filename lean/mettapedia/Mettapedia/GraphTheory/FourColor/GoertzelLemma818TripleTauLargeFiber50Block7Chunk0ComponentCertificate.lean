import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 7 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block7Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block7Chunk0Sources : List Nat :=
  [   5920, 5921, 5922, 5923, 5924, 5925, 5926, 5927,
   5928, 5929, 5930, 5931, 5932, 5933, 5934, 5935]

def tttLargeFiber50Row448 : TripleComponentParentRow :=
  tripleRow 5920 5792 175 72 80 173 140 148
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

def tttLargeFiber50Row449 : TripleComponentParentRow :=
  tripleRow 5921 5793 175 72 81 173 140 149
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

def tttLargeFiber50Row450 : TripleComponentParentRow :=
  tripleRow 5922 5920 175 72 82 175 72 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row451 : TripleComponentParentRow :=
  tripleRow 5923 5795 175 72 83 173 140 151
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row452 : TripleComponentParentRow :=
  tripleRow 5924 5796 175 72 100 173 140 164
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

def tttLargeFiber50Row453 : TripleComponentParentRow :=
  tripleRow 5925 5797 175 72 101 173 140 165
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

def tttLargeFiber50Row454 : TripleComponentParentRow :=
  tripleRow 5926 5921 175 72 102 175 72 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row455 : TripleComponentParentRow :=
  tripleRow 5927 5920 175 72 103 175 72 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Row456 : TripleComponentParentRow :=
  tripleRow 5928 5800 175 73 88 173 141 156
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

def tttLargeFiber50Row457 : TripleComponentParentRow :=
  tripleRow 5929 5801 175 73 89 173 141 157
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

def tttLargeFiber50Row458 : TripleComponentParentRow :=
  tripleRow 5930 5928 175 73 90 175 73 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row459 : TripleComponentParentRow :=
  tripleRow 5931 5803 175 73 91 173 141 159
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row460 : TripleComponentParentRow :=
  tripleRow 5932 5804 175 73 108 173 141 172
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

def tttLargeFiber50Row461 : TripleComponentParentRow :=
  tripleRow 5933 5805 175 73 109 173 141 173
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

def tttLargeFiber50Row462 : TripleComponentParentRow :=
  tripleRow 5934 5929 175 73 110 175 73 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row463 : TripleComponentParentRow :=
  tripleRow 5935 5928 175 73 111 175 73 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Block7Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row448
  , tttLargeFiber50Row449
  , tttLargeFiber50Row450
  , tttLargeFiber50Row451
  , tttLargeFiber50Row452
  , tttLargeFiber50Row453
  , tttLargeFiber50Row454
  , tttLargeFiber50Row455
  , tttLargeFiber50Row456
  , tttLargeFiber50Row457
  , tttLargeFiber50Row458
  , tttLargeFiber50Row459
  , tttLargeFiber50Row460
  , tttLargeFiber50Row461
  , tttLargeFiber50Row462
  , tttLargeFiber50Row463
  ]

def tttLargeFiber50Block7Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block7Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block7Chunk0ExpectedContains row.source &&
    tttLargeFiber50Block7Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block7Chunk0SourcesCheck : Bool :=
  (tttLargeFiber50Block7Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber50Block7Chunk0Sources

theorem tttLargeFiber50Block7Chunk0SourcesCheck_ok :
    tttLargeFiber50Block7Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber50Block7Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block7Chunk0RowValid
    (listGetD tttLargeFiber50Block7Chunk0Rows i default)

def tttLargeFiber50Block7Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block7Chunk0Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block7Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block7Chunk0Sources 0 0 == 5920
      && tttLargeFiber50ParentOf 5920 == 5792
      && tttLargeFiber50ParentOf 5792 == 5248
      && tttLargeFiber50ParentOf 5248 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block7Chunk0Sources 1 0 == 5921
      && tttLargeFiber50ParentOf 5921 == 5793
      && tttLargeFiber50ParentOf 5793 == 5249
      && tttLargeFiber50ParentOf 5249 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block7Chunk0Sources 2 0 == 5922
      && tttLargeFiber50ParentOf 5922 == 5920
      && tttLargeFiber50ParentOf 5920 == 5792
      && tttLargeFiber50ParentOf 5792 == 5248
      && tttLargeFiber50ParentOf 5248 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block7Chunk0Sources 3 0 == 5923
      && tttLargeFiber50ParentOf 5923 == 5795
      && tttLargeFiber50ParentOf 5795 == 5251
      && tttLargeFiber50ParentOf 5251 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block7Chunk0Sources 4 0 == 5924
      && tttLargeFiber50ParentOf 5924 == 5796
      && tttLargeFiber50ParentOf 5796 == 5252
      && tttLargeFiber50ParentOf 5252 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block7Chunk0Sources 5 0 == 5925
      && tttLargeFiber50ParentOf 5925 == 5797
      && tttLargeFiber50ParentOf 5797 == 5253
      && tttLargeFiber50ParentOf 5253 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block7Chunk0Sources 6 0 == 5926
      && tttLargeFiber50ParentOf 5926 == 5921
      && tttLargeFiber50ParentOf 5921 == 5793
      && tttLargeFiber50ParentOf 5793 == 5249
      && tttLargeFiber50ParentOf 5249 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block7Chunk0Sources 7 0 == 5927
      && tttLargeFiber50ParentOf 5927 == 5920
      && tttLargeFiber50ParentOf 5920 == 5792
      && tttLargeFiber50ParentOf 5792 == 5248
      && tttLargeFiber50ParentOf 5248 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block7Chunk0Sources 8 0 == 5928
      && tttLargeFiber50ParentOf 5928 == 5800
      && tttLargeFiber50ParentOf 5800 == 5256
      && tttLargeFiber50ParentOf 5256 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block7Chunk0Sources 9 0 == 5929
      && tttLargeFiber50ParentOf 5929 == 5801
      && tttLargeFiber50ParentOf 5801 == 5257
      && tttLargeFiber50ParentOf 5257 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block7Chunk0Sources 10 0 == 5930
      && tttLargeFiber50ParentOf 5930 == 5928
      && tttLargeFiber50ParentOf 5928 == 5800
      && tttLargeFiber50ParentOf 5800 == 5256
      && tttLargeFiber50ParentOf 5256 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block7Chunk0Sources 11 0 == 5931
      && tttLargeFiber50ParentOf 5931 == 5803
      && tttLargeFiber50ParentOf 5803 == 5259
      && tttLargeFiber50ParentOf 5259 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block7Chunk0Sources 12 0 == 5932
      && tttLargeFiber50ParentOf 5932 == 5804
      && tttLargeFiber50ParentOf 5804 == 5260
      && tttLargeFiber50ParentOf 5260 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block7Chunk0Sources 13 0 == 5933
      && tttLargeFiber50ParentOf 5933 == 5805
      && tttLargeFiber50ParentOf 5805 == 5261
      && tttLargeFiber50ParentOf 5261 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (6 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block7Chunk0Sources 14 0 == 5934
      && tttLargeFiber50ParentOf 5934 == 5929
      && tttLargeFiber50ParentOf 5929 == 5801
      && tttLargeFiber50ParentOf 5801 == 5257
      && tttLargeFiber50ParentOf 5257 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (6 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block7Chunk0Sources 15 0 == 5935
      && tttLargeFiber50ParentOf 5935 == 5928
      && tttLargeFiber50ParentOf 5928 == 5800
      && tttLargeFiber50ParentOf 5800 == 5256
      && tttLargeFiber50ParentOf 5256 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block7Chunk0Row_0_ok :
    tttLargeFiber50Block7Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_1_ok :
    tttLargeFiber50Block7Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_2_ok :
    tttLargeFiber50Block7Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_3_ok :
    tttLargeFiber50Block7Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_4_ok :
    tttLargeFiber50Block7Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_5_ok :
    tttLargeFiber50Block7Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_6_ok :
    tttLargeFiber50Block7Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_7_ok :
    tttLargeFiber50Block7Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_8_ok :
    tttLargeFiber50Block7Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_9_ok :
    tttLargeFiber50Block7Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_10_ok :
    tttLargeFiber50Block7Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_11_ok :
    tttLargeFiber50Block7Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_12_ok :
    tttLargeFiber50Block7Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_13_ok :
    tttLargeFiber50Block7Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_14_ok :
    tttLargeFiber50Block7Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0Row_15_ok :
    tttLargeFiber50Block7Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_0_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_1_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_2_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_3_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_4_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_5_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_6_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_7_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_8_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_9_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_10_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_11_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_12_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_13_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_14_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentMap_15_ok :
    tttLargeFiber50Block7Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_0_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_1_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_2_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_3_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_4_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_5_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_6_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_7_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_8_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_9_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_10_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_11_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_12_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_13_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_14_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block7Chunk0ParentPath_15_ok :
    tttLargeFiber50Block7Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block7Chunk0RowsAudit : Bool :=
  tttLargeFiber50Block7Chunk0RowCheck 0
    && tttLargeFiber50Block7Chunk0RowCheck 1
    && tttLargeFiber50Block7Chunk0RowCheck 2
    && tttLargeFiber50Block7Chunk0RowCheck 3
    && tttLargeFiber50Block7Chunk0RowCheck 4
    && tttLargeFiber50Block7Chunk0RowCheck 5
    && tttLargeFiber50Block7Chunk0RowCheck 6
    && tttLargeFiber50Block7Chunk0RowCheck 7
    && tttLargeFiber50Block7Chunk0RowCheck 8
    && tttLargeFiber50Block7Chunk0RowCheck 9
    && tttLargeFiber50Block7Chunk0RowCheck 10
    && tttLargeFiber50Block7Chunk0RowCheck 11
    && tttLargeFiber50Block7Chunk0RowCheck 12
    && tttLargeFiber50Block7Chunk0RowCheck 13
    && tttLargeFiber50Block7Chunk0RowCheck 14
    && tttLargeFiber50Block7Chunk0RowCheck 15

theorem tttLargeFiber50Block7Chunk0RowsAudit_ok :
    tttLargeFiber50Block7Chunk0RowsAudit = true := by
  simp [tttLargeFiber50Block7Chunk0RowsAudit,
    tttLargeFiber50Block7Chunk0Row_0_ok,
    tttLargeFiber50Block7Chunk0Row_1_ok,
    tttLargeFiber50Block7Chunk0Row_2_ok,
    tttLargeFiber50Block7Chunk0Row_3_ok,
    tttLargeFiber50Block7Chunk0Row_4_ok,
    tttLargeFiber50Block7Chunk0Row_5_ok,
    tttLargeFiber50Block7Chunk0Row_6_ok,
    tttLargeFiber50Block7Chunk0Row_7_ok,
    tttLargeFiber50Block7Chunk0Row_8_ok,
    tttLargeFiber50Block7Chunk0Row_9_ok,
    tttLargeFiber50Block7Chunk0Row_10_ok,
    tttLargeFiber50Block7Chunk0Row_11_ok,
    tttLargeFiber50Block7Chunk0Row_12_ok,
    tttLargeFiber50Block7Chunk0Row_13_ok,
    tttLargeFiber50Block7Chunk0Row_14_ok,
    tttLargeFiber50Block7Chunk0Row_15_ok]

def tttLargeFiber50Block7Chunk0ParentMapAudit : Bool :=
  tttLargeFiber50Block7Chunk0ParentMapCheck 0
    && tttLargeFiber50Block7Chunk0ParentMapCheck 1
    && tttLargeFiber50Block7Chunk0ParentMapCheck 2
    && tttLargeFiber50Block7Chunk0ParentMapCheck 3
    && tttLargeFiber50Block7Chunk0ParentMapCheck 4
    && tttLargeFiber50Block7Chunk0ParentMapCheck 5
    && tttLargeFiber50Block7Chunk0ParentMapCheck 6
    && tttLargeFiber50Block7Chunk0ParentMapCheck 7
    && tttLargeFiber50Block7Chunk0ParentMapCheck 8
    && tttLargeFiber50Block7Chunk0ParentMapCheck 9
    && tttLargeFiber50Block7Chunk0ParentMapCheck 10
    && tttLargeFiber50Block7Chunk0ParentMapCheck 11
    && tttLargeFiber50Block7Chunk0ParentMapCheck 12
    && tttLargeFiber50Block7Chunk0ParentMapCheck 13
    && tttLargeFiber50Block7Chunk0ParentMapCheck 14
    && tttLargeFiber50Block7Chunk0ParentMapCheck 15

theorem tttLargeFiber50Block7Chunk0ParentMapAudit_ok :
    tttLargeFiber50Block7Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber50Block7Chunk0ParentMapAudit,
    tttLargeFiber50Block7Chunk0ParentMap_0_ok,
    tttLargeFiber50Block7Chunk0ParentMap_1_ok,
    tttLargeFiber50Block7Chunk0ParentMap_2_ok,
    tttLargeFiber50Block7Chunk0ParentMap_3_ok,
    tttLargeFiber50Block7Chunk0ParentMap_4_ok,
    tttLargeFiber50Block7Chunk0ParentMap_5_ok,
    tttLargeFiber50Block7Chunk0ParentMap_6_ok,
    tttLargeFiber50Block7Chunk0ParentMap_7_ok,
    tttLargeFiber50Block7Chunk0ParentMap_8_ok,
    tttLargeFiber50Block7Chunk0ParentMap_9_ok,
    tttLargeFiber50Block7Chunk0ParentMap_10_ok,
    tttLargeFiber50Block7Chunk0ParentMap_11_ok,
    tttLargeFiber50Block7Chunk0ParentMap_12_ok,
    tttLargeFiber50Block7Chunk0ParentMap_13_ok,
    tttLargeFiber50Block7Chunk0ParentMap_14_ok,
    tttLargeFiber50Block7Chunk0ParentMap_15_ok]

def tttLargeFiber50Block7Chunk0ParentsAudit : Bool :=
  tttLargeFiber50Block7Chunk0ParentPathCheck 0
    && tttLargeFiber50Block7Chunk0ParentPathCheck 1
    && tttLargeFiber50Block7Chunk0ParentPathCheck 2
    && tttLargeFiber50Block7Chunk0ParentPathCheck 3
    && tttLargeFiber50Block7Chunk0ParentPathCheck 4
    && tttLargeFiber50Block7Chunk0ParentPathCheck 5
    && tttLargeFiber50Block7Chunk0ParentPathCheck 6
    && tttLargeFiber50Block7Chunk0ParentPathCheck 7
    && tttLargeFiber50Block7Chunk0ParentPathCheck 8
    && tttLargeFiber50Block7Chunk0ParentPathCheck 9
    && tttLargeFiber50Block7Chunk0ParentPathCheck 10
    && tttLargeFiber50Block7Chunk0ParentPathCheck 11
    && tttLargeFiber50Block7Chunk0ParentPathCheck 12
    && tttLargeFiber50Block7Chunk0ParentPathCheck 13
    && tttLargeFiber50Block7Chunk0ParentPathCheck 14
    && tttLargeFiber50Block7Chunk0ParentPathCheck 15

theorem tttLargeFiber50Block7Chunk0ParentsAudit_ok :
    tttLargeFiber50Block7Chunk0ParentsAudit = true := by
  simp [tttLargeFiber50Block7Chunk0ParentsAudit,
    tttLargeFiber50Block7Chunk0ParentPath_0_ok,
    tttLargeFiber50Block7Chunk0ParentPath_1_ok,
    tttLargeFiber50Block7Chunk0ParentPath_2_ok,
    tttLargeFiber50Block7Chunk0ParentPath_3_ok,
    tttLargeFiber50Block7Chunk0ParentPath_4_ok,
    tttLargeFiber50Block7Chunk0ParentPath_5_ok,
    tttLargeFiber50Block7Chunk0ParentPath_6_ok,
    tttLargeFiber50Block7Chunk0ParentPath_7_ok,
    tttLargeFiber50Block7Chunk0ParentPath_8_ok,
    tttLargeFiber50Block7Chunk0ParentPath_9_ok,
    tttLargeFiber50Block7Chunk0ParentPath_10_ok,
    tttLargeFiber50Block7Chunk0ParentPath_11_ok,
    tttLargeFiber50Block7Chunk0ParentPath_12_ok,
    tttLargeFiber50Block7Chunk0ParentPath_13_ok,
    tttLargeFiber50Block7Chunk0ParentPath_14_ok,
    tttLargeFiber50Block7Chunk0ParentPath_15_ok]

def tttLargeFiber50Block7Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block7Chunk0SourcesCheck &&
    tttLargeFiber50Block7Chunk0RowsAudit &&
    tttLargeFiber50Block7Chunk0ParentMapAudit &&
    tttLargeFiber50Block7Chunk0ParentsAudit

theorem tttLargeFiber50Block7Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber50Block7Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block7Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block7Chunk0SourcesCheck_ok,
    tttLargeFiber50Block7Chunk0RowsAudit_ok,
    tttLargeFiber50Block7Chunk0ParentMapAudit_ok,
    tttLargeFiber50Block7Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block7Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
