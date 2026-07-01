import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 7 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block7Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block7Chunk3Sources : List Nat :=
  [   5968, 5969, 5970, 5971, 5972, 5973, 5974, 5975,
   5976, 5977, 5978, 5979, 5980, 5981, 5982, 5983]

def tttLargeFiber50Row496 : TripleComponentParentRow :=
  tripleRow 5968 5952 175 126 64 175 124 132
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

def tttLargeFiber50Row497 : TripleComponentParentRow :=
  tripleRow 5969 5953 175 126 65 175 124 133
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

def tttLargeFiber50Row498 : TripleComponentParentRow :=
  tripleRow 5970 5968 175 126 66 175 126 64
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row499 : TripleComponentParentRow :=
  tripleRow 5971 5955 175 126 67 175 124 135
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

def tttLargeFiber50Row500 : TripleComponentParentRow :=
  tripleRow 5972 5956 175 126 116 175 124 180
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row501 : TripleComponentParentRow :=
  tripleRow 5973 5957 175 126 117 175 124 181
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row502 : TripleComponentParentRow :=
  tripleRow 5974 5969 175 126 118 175 126 65
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row503 : TripleComponentParentRow :=
  tripleRow 5975 5968 175 126 119 175 126 64
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Row504 : TripleComponentParentRow :=
  tripleRow 5976 5960 175 127 72 175 125 140
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

def tttLargeFiber50Row505 : TripleComponentParentRow :=
  tripleRow 5977 5961 175 127 73 175 125 141
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

def tttLargeFiber50Row506 : TripleComponentParentRow :=
  tripleRow 5978 5434 175 127 74 159 59 10
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber50Row507 : TripleComponentParentRow :=
  tripleRow 5979 5435 175 127 75 159 59 11
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber50Row508 : TripleComponentParentRow :=
  tripleRow 5980 5436 175 127 124 159 59 56
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber50Row509 : TripleComponentParentRow :=
  tripleRow 5981 5437 175 127 125 159 59 57
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber50Row510 : TripleComponentParentRow :=
  tripleRow 5982 5980 175 127 126 175 127 124
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row511 : TripleComponentParentRow :=
  tripleRow 5983 5439 175 127 127 159 59 59
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber50Block7Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row496
  , tttLargeFiber50Row497
  , tttLargeFiber50Row498
  , tttLargeFiber50Row499
  , tttLargeFiber50Row500
  , tttLargeFiber50Row501
  , tttLargeFiber50Row502
  , tttLargeFiber50Row503
  , tttLargeFiber50Row504
  , tttLargeFiber50Row505
  , tttLargeFiber50Row506
  , tttLargeFiber50Row507
  , tttLargeFiber50Row508
  , tttLargeFiber50Row509
  , tttLargeFiber50Row510
  , tttLargeFiber50Row511
  ]

def tttLargeFiber50Block7Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block7Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block7Chunk3ExpectedContains row.source &&
    tttLargeFiber50Block7Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block7Chunk3SourcesCheck : Bool :=
  (tttLargeFiber50Block7Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber50Block7Chunk3Sources

theorem tttLargeFiber50Block7Chunk3SourcesCheck_ok :
    tttLargeFiber50Block7Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber50Block7Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block7Chunk3RowValid
    (listGetD tttLargeFiber50Block7Chunk3Rows i default)

def tttLargeFiber50Block7Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block7Chunk3Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block7Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block7Chunk3Sources 0 0 == 5968
      && tttLargeFiber50ParentOf 5968 == 5952
      && tttLargeFiber50ParentOf 5952 == 5408
      && tttLargeFiber50ParentOf 5408 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block7Chunk3Sources 1 0 == 5969
      && tttLargeFiber50ParentOf 5969 == 5953
      && tttLargeFiber50ParentOf 5953 == 5409
      && tttLargeFiber50ParentOf 5409 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block7Chunk3Sources 2 0 == 5970
      && tttLargeFiber50ParentOf 5970 == 5968
      && tttLargeFiber50ParentOf 5968 == 5952
      && tttLargeFiber50ParentOf 5952 == 5408
      && tttLargeFiber50ParentOf 5408 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block7Chunk3Sources 3 0 == 5971
      && tttLargeFiber50ParentOf 5971 == 5955
      && tttLargeFiber50ParentOf 5955 == 5411
      && tttLargeFiber50ParentOf 5411 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block7Chunk3Sources 4 0 == 5972
      && tttLargeFiber50ParentOf 5972 == 5956
      && tttLargeFiber50ParentOf 5956 == 5412
      && tttLargeFiber50ParentOf 5412 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block7Chunk3Sources 5 0 == 5973
      && tttLargeFiber50ParentOf 5973 == 5957
      && tttLargeFiber50ParentOf 5957 == 5413
      && tttLargeFiber50ParentOf 5413 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block7Chunk3Sources 6 0 == 5974
      && tttLargeFiber50ParentOf 5974 == 5969
      && tttLargeFiber50ParentOf 5969 == 5953
      && tttLargeFiber50ParentOf 5953 == 5409
      && tttLargeFiber50ParentOf 5409 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block7Chunk3Sources 7 0 == 5975
      && tttLargeFiber50ParentOf 5975 == 5968
      && tttLargeFiber50ParentOf 5968 == 5952
      && tttLargeFiber50ParentOf 5952 == 5408
      && tttLargeFiber50ParentOf 5408 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block7Chunk3Sources 8 0 == 5976
      && tttLargeFiber50ParentOf 5976 == 5960
      && tttLargeFiber50ParentOf 5960 == 5416
      && tttLargeFiber50ParentOf 5416 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block7Chunk3Sources 9 0 == 5977
      && tttLargeFiber50ParentOf 5977 == 5961
      && tttLargeFiber50ParentOf 5961 == 5417
      && tttLargeFiber50ParentOf 5417 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block7Chunk3Sources 10 0 == 5978
      && tttLargeFiber50ParentOf 5978 == 5434
      && tttLargeFiber50ParentOf 5434 == 5210
      && tttLargeFiber50ParentOf 5210 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block7Chunk3Sources 11 0 == 5979
      && tttLargeFiber50ParentOf 5979 == 5435
      && tttLargeFiber50ParentOf 5435 == 5211
      && tttLargeFiber50ParentOf 5211 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block7Chunk3Sources 12 0 == 5980
      && tttLargeFiber50ParentOf 5980 == 5436
      && tttLargeFiber50ParentOf 5436 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block7Chunk3Sources 13 0 == 5981
      && tttLargeFiber50ParentOf 5981 == 5437
      && tttLargeFiber50ParentOf 5437 == 5213
      && tttLargeFiber50ParentOf 5213 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block7Chunk3Sources 14 0 == 5982
      && tttLargeFiber50ParentOf 5982 == 5980
      && tttLargeFiber50ParentOf 5980 == 5436
      && tttLargeFiber50ParentOf 5436 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block7Chunk3Sources 15 0 == 5983
      && tttLargeFiber50ParentOf 5983 == 5439
      && tttLargeFiber50ParentOf 5439 == 5215
      && tttLargeFiber50ParentOf 5215 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block7Chunk3Row_0_ok :
    tttLargeFiber50Block7Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_1_ok :
    tttLargeFiber50Block7Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_2_ok :
    tttLargeFiber50Block7Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_3_ok :
    tttLargeFiber50Block7Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_4_ok :
    tttLargeFiber50Block7Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_5_ok :
    tttLargeFiber50Block7Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_6_ok :
    tttLargeFiber50Block7Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_7_ok :
    tttLargeFiber50Block7Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_8_ok :
    tttLargeFiber50Block7Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_9_ok :
    tttLargeFiber50Block7Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_10_ok :
    tttLargeFiber50Block7Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_11_ok :
    tttLargeFiber50Block7Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_12_ok :
    tttLargeFiber50Block7Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_13_ok :
    tttLargeFiber50Block7Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_14_ok :
    tttLargeFiber50Block7Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3Row_15_ok :
    tttLargeFiber50Block7Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_0_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_1_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_2_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_3_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_4_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_5_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_6_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_7_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_8_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_9_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_10_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_11_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_12_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_13_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_14_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentMap_15_ok :
    tttLargeFiber50Block7Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_0_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_1_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_2_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_3_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_4_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_5_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_6_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_7_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_8_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_9_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_10_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_11_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_12_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_13_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_14_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block7Chunk3ParentPath_15_ok :
    tttLargeFiber50Block7Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block7Chunk3RowsAudit : Bool :=
  tttLargeFiber50Block7Chunk3RowCheck 0
    && tttLargeFiber50Block7Chunk3RowCheck 1
    && tttLargeFiber50Block7Chunk3RowCheck 2
    && tttLargeFiber50Block7Chunk3RowCheck 3
    && tttLargeFiber50Block7Chunk3RowCheck 4
    && tttLargeFiber50Block7Chunk3RowCheck 5
    && tttLargeFiber50Block7Chunk3RowCheck 6
    && tttLargeFiber50Block7Chunk3RowCheck 7
    && tttLargeFiber50Block7Chunk3RowCheck 8
    && tttLargeFiber50Block7Chunk3RowCheck 9
    && tttLargeFiber50Block7Chunk3RowCheck 10
    && tttLargeFiber50Block7Chunk3RowCheck 11
    && tttLargeFiber50Block7Chunk3RowCheck 12
    && tttLargeFiber50Block7Chunk3RowCheck 13
    && tttLargeFiber50Block7Chunk3RowCheck 14
    && tttLargeFiber50Block7Chunk3RowCheck 15

theorem tttLargeFiber50Block7Chunk3RowsAudit_ok :
    tttLargeFiber50Block7Chunk3RowsAudit = true := by
  simp [tttLargeFiber50Block7Chunk3RowsAudit,
    tttLargeFiber50Block7Chunk3Row_0_ok,
    tttLargeFiber50Block7Chunk3Row_1_ok,
    tttLargeFiber50Block7Chunk3Row_2_ok,
    tttLargeFiber50Block7Chunk3Row_3_ok,
    tttLargeFiber50Block7Chunk3Row_4_ok,
    tttLargeFiber50Block7Chunk3Row_5_ok,
    tttLargeFiber50Block7Chunk3Row_6_ok,
    tttLargeFiber50Block7Chunk3Row_7_ok,
    tttLargeFiber50Block7Chunk3Row_8_ok,
    tttLargeFiber50Block7Chunk3Row_9_ok,
    tttLargeFiber50Block7Chunk3Row_10_ok,
    tttLargeFiber50Block7Chunk3Row_11_ok,
    tttLargeFiber50Block7Chunk3Row_12_ok,
    tttLargeFiber50Block7Chunk3Row_13_ok,
    tttLargeFiber50Block7Chunk3Row_14_ok,
    tttLargeFiber50Block7Chunk3Row_15_ok]

def tttLargeFiber50Block7Chunk3ParentMapAudit : Bool :=
  tttLargeFiber50Block7Chunk3ParentMapCheck 0
    && tttLargeFiber50Block7Chunk3ParentMapCheck 1
    && tttLargeFiber50Block7Chunk3ParentMapCheck 2
    && tttLargeFiber50Block7Chunk3ParentMapCheck 3
    && tttLargeFiber50Block7Chunk3ParentMapCheck 4
    && tttLargeFiber50Block7Chunk3ParentMapCheck 5
    && tttLargeFiber50Block7Chunk3ParentMapCheck 6
    && tttLargeFiber50Block7Chunk3ParentMapCheck 7
    && tttLargeFiber50Block7Chunk3ParentMapCheck 8
    && tttLargeFiber50Block7Chunk3ParentMapCheck 9
    && tttLargeFiber50Block7Chunk3ParentMapCheck 10
    && tttLargeFiber50Block7Chunk3ParentMapCheck 11
    && tttLargeFiber50Block7Chunk3ParentMapCheck 12
    && tttLargeFiber50Block7Chunk3ParentMapCheck 13
    && tttLargeFiber50Block7Chunk3ParentMapCheck 14
    && tttLargeFiber50Block7Chunk3ParentMapCheck 15

theorem tttLargeFiber50Block7Chunk3ParentMapAudit_ok :
    tttLargeFiber50Block7Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber50Block7Chunk3ParentMapAudit,
    tttLargeFiber50Block7Chunk3ParentMap_0_ok,
    tttLargeFiber50Block7Chunk3ParentMap_1_ok,
    tttLargeFiber50Block7Chunk3ParentMap_2_ok,
    tttLargeFiber50Block7Chunk3ParentMap_3_ok,
    tttLargeFiber50Block7Chunk3ParentMap_4_ok,
    tttLargeFiber50Block7Chunk3ParentMap_5_ok,
    tttLargeFiber50Block7Chunk3ParentMap_6_ok,
    tttLargeFiber50Block7Chunk3ParentMap_7_ok,
    tttLargeFiber50Block7Chunk3ParentMap_8_ok,
    tttLargeFiber50Block7Chunk3ParentMap_9_ok,
    tttLargeFiber50Block7Chunk3ParentMap_10_ok,
    tttLargeFiber50Block7Chunk3ParentMap_11_ok,
    tttLargeFiber50Block7Chunk3ParentMap_12_ok,
    tttLargeFiber50Block7Chunk3ParentMap_13_ok,
    tttLargeFiber50Block7Chunk3ParentMap_14_ok,
    tttLargeFiber50Block7Chunk3ParentMap_15_ok]

def tttLargeFiber50Block7Chunk3ParentsAudit : Bool :=
  tttLargeFiber50Block7Chunk3ParentPathCheck 0
    && tttLargeFiber50Block7Chunk3ParentPathCheck 1
    && tttLargeFiber50Block7Chunk3ParentPathCheck 2
    && tttLargeFiber50Block7Chunk3ParentPathCheck 3
    && tttLargeFiber50Block7Chunk3ParentPathCheck 4
    && tttLargeFiber50Block7Chunk3ParentPathCheck 5
    && tttLargeFiber50Block7Chunk3ParentPathCheck 6
    && tttLargeFiber50Block7Chunk3ParentPathCheck 7
    && tttLargeFiber50Block7Chunk3ParentPathCheck 8
    && tttLargeFiber50Block7Chunk3ParentPathCheck 9
    && tttLargeFiber50Block7Chunk3ParentPathCheck 10
    && tttLargeFiber50Block7Chunk3ParentPathCheck 11
    && tttLargeFiber50Block7Chunk3ParentPathCheck 12
    && tttLargeFiber50Block7Chunk3ParentPathCheck 13
    && tttLargeFiber50Block7Chunk3ParentPathCheck 14
    && tttLargeFiber50Block7Chunk3ParentPathCheck 15

theorem tttLargeFiber50Block7Chunk3ParentsAudit_ok :
    tttLargeFiber50Block7Chunk3ParentsAudit = true := by
  simp [tttLargeFiber50Block7Chunk3ParentsAudit,
    tttLargeFiber50Block7Chunk3ParentPath_0_ok,
    tttLargeFiber50Block7Chunk3ParentPath_1_ok,
    tttLargeFiber50Block7Chunk3ParentPath_2_ok,
    tttLargeFiber50Block7Chunk3ParentPath_3_ok,
    tttLargeFiber50Block7Chunk3ParentPath_4_ok,
    tttLargeFiber50Block7Chunk3ParentPath_5_ok,
    tttLargeFiber50Block7Chunk3ParentPath_6_ok,
    tttLargeFiber50Block7Chunk3ParentPath_7_ok,
    tttLargeFiber50Block7Chunk3ParentPath_8_ok,
    tttLargeFiber50Block7Chunk3ParentPath_9_ok,
    tttLargeFiber50Block7Chunk3ParentPath_10_ok,
    tttLargeFiber50Block7Chunk3ParentPath_11_ok,
    tttLargeFiber50Block7Chunk3ParentPath_12_ok,
    tttLargeFiber50Block7Chunk3ParentPath_13_ok,
    tttLargeFiber50Block7Chunk3ParentPath_14_ok,
    tttLargeFiber50Block7Chunk3ParentPath_15_ok]

def tttLargeFiber50Block7Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block7Chunk3SourcesCheck &&
    tttLargeFiber50Block7Chunk3RowsAudit &&
    tttLargeFiber50Block7Chunk3ParentMapAudit &&
    tttLargeFiber50Block7Chunk3ParentsAudit

theorem tttLargeFiber50Block7Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber50Block7Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block7Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block7Chunk3SourcesCheck_ok,
    tttLargeFiber50Block7Chunk3RowsAudit_ok,
    tttLargeFiber50Block7Chunk3ParentMapAudit_ok,
    tttLargeFiber50Block7Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block7Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
