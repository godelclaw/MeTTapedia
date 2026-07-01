import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 6 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block6Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block6Chunk0Sources : List Nat :=
  [   5856, 5857, 5858, 5859, 5860, 5861, 5862, 5863,
   5864, 5865, 5866, 5867, 5868, 5869, 5870, 5871]

def tttLargeFiber50Row384 : TripleComponentParentRow :=
  tripleRow 5856 5728 174 64 80 172 132 148
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

def tttLargeFiber50Row385 : TripleComponentParentRow :=
  tripleRow 5857 5729 174 64 81 172 132 149
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

def tttLargeFiber50Row386 : TripleComponentParentRow :=
  tripleRow 5858 5856 174 64 82 174 64 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row387 : TripleComponentParentRow :=
  tripleRow 5859 5731 174 64 83 172 132 151
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row388 : TripleComponentParentRow :=
  tripleRow 5860 5732 174 64 100 172 132 164
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

def tttLargeFiber50Row389 : TripleComponentParentRow :=
  tripleRow 5861 5733 174 64 101 172 132 165
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

def tttLargeFiber50Row390 : TripleComponentParentRow :=
  tripleRow 5862 5857 174 64 102 174 64 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row391 : TripleComponentParentRow :=
  tripleRow 5863 5856 174 64 103 174 64 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Row392 : TripleComponentParentRow :=
  tripleRow 5864 5736 174 65 88 172 133 156
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

def tttLargeFiber50Row393 : TripleComponentParentRow :=
  tripleRow 5865 5737 174 65 89 172 133 157
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

def tttLargeFiber50Row394 : TripleComponentParentRow :=
  tripleRow 5866 5864 174 65 90 174 65 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row395 : TripleComponentParentRow :=
  tripleRow 5867 5739 174 65 91 172 133 159
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row396 : TripleComponentParentRow :=
  tripleRow 5868 5740 174 65 108 172 133 172
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

def tttLargeFiber50Row397 : TripleComponentParentRow :=
  tripleRow 5869 5741 174 65 109 172 133 173
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

def tttLargeFiber50Row398 : TripleComponentParentRow :=
  tripleRow 5870 5865 174 65 110 174 65 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row399 : TripleComponentParentRow :=
  tripleRow 5871 5864 174 65 111 174 65 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber50Block6Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row384
  , tttLargeFiber50Row385
  , tttLargeFiber50Row386
  , tttLargeFiber50Row387
  , tttLargeFiber50Row388
  , tttLargeFiber50Row389
  , tttLargeFiber50Row390
  , tttLargeFiber50Row391
  , tttLargeFiber50Row392
  , tttLargeFiber50Row393
  , tttLargeFiber50Row394
  , tttLargeFiber50Row395
  , tttLargeFiber50Row396
  , tttLargeFiber50Row397
  , tttLargeFiber50Row398
  , tttLargeFiber50Row399
  ]

def tttLargeFiber50Block6Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block6Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block6Chunk0ExpectedContains row.source &&
    tttLargeFiber50Block6Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block6Chunk0SourcesCheck : Bool :=
  (tttLargeFiber50Block6Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber50Block6Chunk0Sources

theorem tttLargeFiber50Block6Chunk0SourcesCheck_ok :
    tttLargeFiber50Block6Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber50Block6Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block6Chunk0RowValid
    (listGetD tttLargeFiber50Block6Chunk0Rows i default)

def tttLargeFiber50Block6Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block6Chunk0Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block6Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block6Chunk0Sources 0 0 == 5856
      && tttLargeFiber50ParentOf 5856 == 5728
      && tttLargeFiber50ParentOf 5728 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block6Chunk0Sources 1 0 == 5857
      && tttLargeFiber50ParentOf 5857 == 5729
      && tttLargeFiber50ParentOf 5729 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block6Chunk0Sources 2 0 == 5858
      && tttLargeFiber50ParentOf 5858 == 5856
      && tttLargeFiber50ParentOf 5856 == 5728
      && tttLargeFiber50ParentOf 5728 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block6Chunk0Sources 3 0 == 5859
      && tttLargeFiber50ParentOf 5859 == 5731
      && tttLargeFiber50ParentOf 5731 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block6Chunk0Sources 4 0 == 5860
      && tttLargeFiber50ParentOf 5860 == 5732
      && tttLargeFiber50ParentOf 5732 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block6Chunk0Sources 5 0 == 5861
      && tttLargeFiber50ParentOf 5861 == 5733
      && tttLargeFiber50ParentOf 5733 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block6Chunk0Sources 6 0 == 5862
      && tttLargeFiber50ParentOf 5862 == 5857
      && tttLargeFiber50ParentOf 5857 == 5729
      && tttLargeFiber50ParentOf 5729 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block6Chunk0Sources 7 0 == 5863
      && tttLargeFiber50ParentOf 5863 == 5856
      && tttLargeFiber50ParentOf 5856 == 5728
      && tttLargeFiber50ParentOf 5728 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block6Chunk0Sources 8 0 == 5864
      && tttLargeFiber50ParentOf 5864 == 5736
      && tttLargeFiber50ParentOf 5736 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block6Chunk0Sources 9 0 == 5865
      && tttLargeFiber50ParentOf 5865 == 5737
      && tttLargeFiber50ParentOf 5737 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block6Chunk0Sources 10 0 == 5866
      && tttLargeFiber50ParentOf 5866 == 5864
      && tttLargeFiber50ParentOf 5864 == 5736
      && tttLargeFiber50ParentOf 5736 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block6Chunk0Sources 11 0 == 5867
      && tttLargeFiber50ParentOf 5867 == 5739
      && tttLargeFiber50ParentOf 5739 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block6Chunk0Sources 12 0 == 5868
      && tttLargeFiber50ParentOf 5868 == 5740
      && tttLargeFiber50ParentOf 5740 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block6Chunk0Sources 13 0 == 5869
      && tttLargeFiber50ParentOf 5869 == 5741
      && tttLargeFiber50ParentOf 5741 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block6Chunk0Sources 14 0 == 5870
      && tttLargeFiber50ParentOf 5870 == 5865
      && tttLargeFiber50ParentOf 5865 == 5737
      && tttLargeFiber50ParentOf 5737 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block6Chunk0Sources 15 0 == 5871
      && tttLargeFiber50ParentOf 5871 == 5864
      && tttLargeFiber50ParentOf 5864 == 5736
      && tttLargeFiber50ParentOf 5736 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block6Chunk0Row_0_ok :
    tttLargeFiber50Block6Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_1_ok :
    tttLargeFiber50Block6Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_2_ok :
    tttLargeFiber50Block6Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_3_ok :
    tttLargeFiber50Block6Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_4_ok :
    tttLargeFiber50Block6Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_5_ok :
    tttLargeFiber50Block6Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_6_ok :
    tttLargeFiber50Block6Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_7_ok :
    tttLargeFiber50Block6Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_8_ok :
    tttLargeFiber50Block6Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_9_ok :
    tttLargeFiber50Block6Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_10_ok :
    tttLargeFiber50Block6Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_11_ok :
    tttLargeFiber50Block6Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_12_ok :
    tttLargeFiber50Block6Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_13_ok :
    tttLargeFiber50Block6Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_14_ok :
    tttLargeFiber50Block6Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0Row_15_ok :
    tttLargeFiber50Block6Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_0_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_1_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_2_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_3_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_4_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_5_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_6_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_7_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_8_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_9_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_10_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_11_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_12_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_13_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_14_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentMap_15_ok :
    tttLargeFiber50Block6Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_0_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_1_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_2_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_3_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_4_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_5_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_6_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_7_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_8_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_9_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_10_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_11_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_12_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_13_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_14_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block6Chunk0ParentPath_15_ok :
    tttLargeFiber50Block6Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block6Chunk0RowsAudit : Bool :=
  tttLargeFiber50Block6Chunk0RowCheck 0
    && tttLargeFiber50Block6Chunk0RowCheck 1
    && tttLargeFiber50Block6Chunk0RowCheck 2
    && tttLargeFiber50Block6Chunk0RowCheck 3
    && tttLargeFiber50Block6Chunk0RowCheck 4
    && tttLargeFiber50Block6Chunk0RowCheck 5
    && tttLargeFiber50Block6Chunk0RowCheck 6
    && tttLargeFiber50Block6Chunk0RowCheck 7
    && tttLargeFiber50Block6Chunk0RowCheck 8
    && tttLargeFiber50Block6Chunk0RowCheck 9
    && tttLargeFiber50Block6Chunk0RowCheck 10
    && tttLargeFiber50Block6Chunk0RowCheck 11
    && tttLargeFiber50Block6Chunk0RowCheck 12
    && tttLargeFiber50Block6Chunk0RowCheck 13
    && tttLargeFiber50Block6Chunk0RowCheck 14
    && tttLargeFiber50Block6Chunk0RowCheck 15

theorem tttLargeFiber50Block6Chunk0RowsAudit_ok :
    tttLargeFiber50Block6Chunk0RowsAudit = true := by
  simp [tttLargeFiber50Block6Chunk0RowsAudit,
    tttLargeFiber50Block6Chunk0Row_0_ok,
    tttLargeFiber50Block6Chunk0Row_1_ok,
    tttLargeFiber50Block6Chunk0Row_2_ok,
    tttLargeFiber50Block6Chunk0Row_3_ok,
    tttLargeFiber50Block6Chunk0Row_4_ok,
    tttLargeFiber50Block6Chunk0Row_5_ok,
    tttLargeFiber50Block6Chunk0Row_6_ok,
    tttLargeFiber50Block6Chunk0Row_7_ok,
    tttLargeFiber50Block6Chunk0Row_8_ok,
    tttLargeFiber50Block6Chunk0Row_9_ok,
    tttLargeFiber50Block6Chunk0Row_10_ok,
    tttLargeFiber50Block6Chunk0Row_11_ok,
    tttLargeFiber50Block6Chunk0Row_12_ok,
    tttLargeFiber50Block6Chunk0Row_13_ok,
    tttLargeFiber50Block6Chunk0Row_14_ok,
    tttLargeFiber50Block6Chunk0Row_15_ok]

def tttLargeFiber50Block6Chunk0ParentMapAudit : Bool :=
  tttLargeFiber50Block6Chunk0ParentMapCheck 0
    && tttLargeFiber50Block6Chunk0ParentMapCheck 1
    && tttLargeFiber50Block6Chunk0ParentMapCheck 2
    && tttLargeFiber50Block6Chunk0ParentMapCheck 3
    && tttLargeFiber50Block6Chunk0ParentMapCheck 4
    && tttLargeFiber50Block6Chunk0ParentMapCheck 5
    && tttLargeFiber50Block6Chunk0ParentMapCheck 6
    && tttLargeFiber50Block6Chunk0ParentMapCheck 7
    && tttLargeFiber50Block6Chunk0ParentMapCheck 8
    && tttLargeFiber50Block6Chunk0ParentMapCheck 9
    && tttLargeFiber50Block6Chunk0ParentMapCheck 10
    && tttLargeFiber50Block6Chunk0ParentMapCheck 11
    && tttLargeFiber50Block6Chunk0ParentMapCheck 12
    && tttLargeFiber50Block6Chunk0ParentMapCheck 13
    && tttLargeFiber50Block6Chunk0ParentMapCheck 14
    && tttLargeFiber50Block6Chunk0ParentMapCheck 15

theorem tttLargeFiber50Block6Chunk0ParentMapAudit_ok :
    tttLargeFiber50Block6Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber50Block6Chunk0ParentMapAudit,
    tttLargeFiber50Block6Chunk0ParentMap_0_ok,
    tttLargeFiber50Block6Chunk0ParentMap_1_ok,
    tttLargeFiber50Block6Chunk0ParentMap_2_ok,
    tttLargeFiber50Block6Chunk0ParentMap_3_ok,
    tttLargeFiber50Block6Chunk0ParentMap_4_ok,
    tttLargeFiber50Block6Chunk0ParentMap_5_ok,
    tttLargeFiber50Block6Chunk0ParentMap_6_ok,
    tttLargeFiber50Block6Chunk0ParentMap_7_ok,
    tttLargeFiber50Block6Chunk0ParentMap_8_ok,
    tttLargeFiber50Block6Chunk0ParentMap_9_ok,
    tttLargeFiber50Block6Chunk0ParentMap_10_ok,
    tttLargeFiber50Block6Chunk0ParentMap_11_ok,
    tttLargeFiber50Block6Chunk0ParentMap_12_ok,
    tttLargeFiber50Block6Chunk0ParentMap_13_ok,
    tttLargeFiber50Block6Chunk0ParentMap_14_ok,
    tttLargeFiber50Block6Chunk0ParentMap_15_ok]

def tttLargeFiber50Block6Chunk0ParentsAudit : Bool :=
  tttLargeFiber50Block6Chunk0ParentPathCheck 0
    && tttLargeFiber50Block6Chunk0ParentPathCheck 1
    && tttLargeFiber50Block6Chunk0ParentPathCheck 2
    && tttLargeFiber50Block6Chunk0ParentPathCheck 3
    && tttLargeFiber50Block6Chunk0ParentPathCheck 4
    && tttLargeFiber50Block6Chunk0ParentPathCheck 5
    && tttLargeFiber50Block6Chunk0ParentPathCheck 6
    && tttLargeFiber50Block6Chunk0ParentPathCheck 7
    && tttLargeFiber50Block6Chunk0ParentPathCheck 8
    && tttLargeFiber50Block6Chunk0ParentPathCheck 9
    && tttLargeFiber50Block6Chunk0ParentPathCheck 10
    && tttLargeFiber50Block6Chunk0ParentPathCheck 11
    && tttLargeFiber50Block6Chunk0ParentPathCheck 12
    && tttLargeFiber50Block6Chunk0ParentPathCheck 13
    && tttLargeFiber50Block6Chunk0ParentPathCheck 14
    && tttLargeFiber50Block6Chunk0ParentPathCheck 15

theorem tttLargeFiber50Block6Chunk0ParentsAudit_ok :
    tttLargeFiber50Block6Chunk0ParentsAudit = true := by
  simp [tttLargeFiber50Block6Chunk0ParentsAudit,
    tttLargeFiber50Block6Chunk0ParentPath_0_ok,
    tttLargeFiber50Block6Chunk0ParentPath_1_ok,
    tttLargeFiber50Block6Chunk0ParentPath_2_ok,
    tttLargeFiber50Block6Chunk0ParentPath_3_ok,
    tttLargeFiber50Block6Chunk0ParentPath_4_ok,
    tttLargeFiber50Block6Chunk0ParentPath_5_ok,
    tttLargeFiber50Block6Chunk0ParentPath_6_ok,
    tttLargeFiber50Block6Chunk0ParentPath_7_ok,
    tttLargeFiber50Block6Chunk0ParentPath_8_ok,
    tttLargeFiber50Block6Chunk0ParentPath_9_ok,
    tttLargeFiber50Block6Chunk0ParentPath_10_ok,
    tttLargeFiber50Block6Chunk0ParentPath_11_ok,
    tttLargeFiber50Block6Chunk0ParentPath_12_ok,
    tttLargeFiber50Block6Chunk0ParentPath_13_ok,
    tttLargeFiber50Block6Chunk0ParentPath_14_ok,
    tttLargeFiber50Block6Chunk0ParentPath_15_ok]

def tttLargeFiber50Block6Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block6Chunk0SourcesCheck &&
    tttLargeFiber50Block6Chunk0RowsAudit &&
    tttLargeFiber50Block6Chunk0ParentMapAudit &&
    tttLargeFiber50Block6Chunk0ParentsAudit

theorem tttLargeFiber50Block6Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber50Block6Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block6Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block6Chunk0SourcesCheck_ok,
    tttLargeFiber50Block6Chunk0RowsAudit_ok,
    tttLargeFiber50Block6Chunk0ParentMapAudit_ok,
    tttLargeFiber50Block6Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block6Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
