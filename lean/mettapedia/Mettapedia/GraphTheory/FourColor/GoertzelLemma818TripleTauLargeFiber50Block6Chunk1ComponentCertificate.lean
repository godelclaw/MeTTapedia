import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 6 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block6Chunk1Sources : List Nat :=
  [   5872, 5873, 5874, 5875, 5876, 5877, 5878, 5879,
   5880, 5881, 5882, 5883, 5884, 5885, 5886, 5887]

def tttLargeFiber50Row400 : TripleComponentParentRow :=
  tripleRow 5872 5856 174 66 16 174 64 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row401 : TripleComponentParentRow :=
  tripleRow 5873 5857 174 66 17 174 64 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row402 : TripleComponentParentRow :=
  tripleRow 5874 5858 174 66 18 174 64 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row403 : TripleComponentParentRow :=
  tripleRow 5875 5859 174 66 19 174 64 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row404 : TripleComponentParentRow :=
  tripleRow 5876 5860 174 66 32 174 64 100
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber50Row405 : TripleComponentParentRow :=
  tripleRow 5877 5861 174 66 33 174 64 101
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
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

def tttLargeFiber50Row406 : TripleComponentParentRow :=
  tripleRow 5878 5862 174 66 34 174 64 102
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row407 : TripleComponentParentRow :=
  tripleRow 5879 5863 174 66 35 174 64 103
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber50Row408 : TripleComponentParentRow :=
  tripleRow 5880 5864 174 67 24 174 65 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row409 : TripleComponentParentRow :=
  tripleRow 5881 5865 174 67 25 174 65 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber50Row410 : TripleComponentParentRow :=
  tripleRow 5882 5754 174 67 26 172 135 10
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber50Row411 : TripleComponentParentRow :=
  tripleRow 5883 5755 174 67 27 172 135 11
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber50Row412 : TripleComponentParentRow :=
  tripleRow 5884 5756 174 67 40 172 135 56
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber50Row413 : TripleComponentParentRow :=
  tripleRow 5885 5757 174 67 41 172 135 57
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber50Row414 : TripleComponentParentRow :=
  tripleRow 5886 5758 174 67 42 172 135 58
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber50Row415 : TripleComponentParentRow :=
  tripleRow 5887 5759 174 67 43 172 135 59
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber50Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row400
  , tttLargeFiber50Row401
  , tttLargeFiber50Row402
  , tttLargeFiber50Row403
  , tttLargeFiber50Row404
  , tttLargeFiber50Row405
  , tttLargeFiber50Row406
  , tttLargeFiber50Row407
  , tttLargeFiber50Row408
  , tttLargeFiber50Row409
  , tttLargeFiber50Row410
  , tttLargeFiber50Row411
  , tttLargeFiber50Row412
  , tttLargeFiber50Row413
  , tttLargeFiber50Row414
  , tttLargeFiber50Row415
  ]

def tttLargeFiber50Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber50Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber50Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber50Block6Chunk1Sources

theorem tttLargeFiber50Block6Chunk1SourcesCheck_ok :
    tttLargeFiber50Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber50Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block6Chunk1RowValid
    (listGetD tttLargeFiber50Block6Chunk1Rows i default)

def tttLargeFiber50Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block6Chunk1Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block6Chunk1Sources 0 0 == 5872
      && tttLargeFiber50ParentOf 5872 == 5856
      && tttLargeFiber50ParentOf 5856 == 5728
      && tttLargeFiber50ParentOf 5728 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block6Chunk1Sources 1 0 == 5873
      && tttLargeFiber50ParentOf 5873 == 5857
      && tttLargeFiber50ParentOf 5857 == 5729
      && tttLargeFiber50ParentOf 5729 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block6Chunk1Sources 2 0 == 5874
      && tttLargeFiber50ParentOf 5874 == 5858
      && tttLargeFiber50ParentOf 5858 == 5856
      && tttLargeFiber50ParentOf 5856 == 5728
      && tttLargeFiber50ParentOf 5728 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block6Chunk1Sources 3 0 == 5875
      && tttLargeFiber50ParentOf 5875 == 5859
      && tttLargeFiber50ParentOf 5859 == 5731
      && tttLargeFiber50ParentOf 5731 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block6Chunk1Sources 4 0 == 5876
      && tttLargeFiber50ParentOf 5876 == 5860
      && tttLargeFiber50ParentOf 5860 == 5732
      && tttLargeFiber50ParentOf 5732 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block6Chunk1Sources 5 0 == 5877
      && tttLargeFiber50ParentOf 5877 == 5861
      && tttLargeFiber50ParentOf 5861 == 5733
      && tttLargeFiber50ParentOf 5733 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block6Chunk1Sources 6 0 == 5878
      && tttLargeFiber50ParentOf 5878 == 5862
      && tttLargeFiber50ParentOf 5862 == 5857
      && tttLargeFiber50ParentOf 5857 == 5729
      && tttLargeFiber50ParentOf 5729 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block6Chunk1Sources 7 0 == 5879
      && tttLargeFiber50ParentOf 5879 == 5863
      && tttLargeFiber50ParentOf 5863 == 5856
      && tttLargeFiber50ParentOf 5856 == 5728
      && tttLargeFiber50ParentOf 5728 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block6Chunk1Sources 8 0 == 5880
      && tttLargeFiber50ParentOf 5880 == 5864
      && tttLargeFiber50ParentOf 5864 == 5736
      && tttLargeFiber50ParentOf 5736 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block6Chunk1Sources 9 0 == 5881
      && tttLargeFiber50ParentOf 5881 == 5865
      && tttLargeFiber50ParentOf 5865 == 5737
      && tttLargeFiber50ParentOf 5737 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block6Chunk1Sources 10 0 == 5882
      && tttLargeFiber50ParentOf 5882 == 5754
      && tttLargeFiber50ParentOf 5754 == 5210
      && tttLargeFiber50ParentOf 5210 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block6Chunk1Sources 11 0 == 5883
      && tttLargeFiber50ParentOf 5883 == 5755
      && tttLargeFiber50ParentOf 5755 == 5211
      && tttLargeFiber50ParentOf 5211 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block6Chunk1Sources 12 0 == 5884
      && tttLargeFiber50ParentOf 5884 == 5756
      && tttLargeFiber50ParentOf 5756 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block6Chunk1Sources 13 0 == 5885
      && tttLargeFiber50ParentOf 5885 == 5757
      && tttLargeFiber50ParentOf 5757 == 5213
      && tttLargeFiber50ParentOf 5213 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block6Chunk1Sources 14 0 == 5886
      && tttLargeFiber50ParentOf 5886 == 5758
      && tttLargeFiber50ParentOf 5758 == 5214
      && tttLargeFiber50ParentOf 5214 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block6Chunk1Sources 15 0 == 5887
      && tttLargeFiber50ParentOf 5887 == 5759
      && tttLargeFiber50ParentOf 5759 == 5215
      && tttLargeFiber50ParentOf 5215 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block6Chunk1Row_0_ok :
    tttLargeFiber50Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_1_ok :
    tttLargeFiber50Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_2_ok :
    tttLargeFiber50Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_3_ok :
    tttLargeFiber50Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_4_ok :
    tttLargeFiber50Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_5_ok :
    tttLargeFiber50Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_6_ok :
    tttLargeFiber50Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_7_ok :
    tttLargeFiber50Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_8_ok :
    tttLargeFiber50Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_9_ok :
    tttLargeFiber50Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_10_ok :
    tttLargeFiber50Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_11_ok :
    tttLargeFiber50Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_12_ok :
    tttLargeFiber50Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_13_ok :
    tttLargeFiber50Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_14_ok :
    tttLargeFiber50Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1Row_15_ok :
    tttLargeFiber50Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_0_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_1_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_2_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_3_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_4_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_5_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_6_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_7_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_8_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_9_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_10_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_11_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_12_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_13_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_14_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentMap_15_ok :
    tttLargeFiber50Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_0_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_1_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_2_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_3_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_4_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_5_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_6_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_7_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_8_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_9_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_10_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_11_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_12_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_13_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_14_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block6Chunk1ParentPath_15_ok :
    tttLargeFiber50Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber50Block6Chunk1RowCheck 0
    && tttLargeFiber50Block6Chunk1RowCheck 1
    && tttLargeFiber50Block6Chunk1RowCheck 2
    && tttLargeFiber50Block6Chunk1RowCheck 3
    && tttLargeFiber50Block6Chunk1RowCheck 4
    && tttLargeFiber50Block6Chunk1RowCheck 5
    && tttLargeFiber50Block6Chunk1RowCheck 6
    && tttLargeFiber50Block6Chunk1RowCheck 7
    && tttLargeFiber50Block6Chunk1RowCheck 8
    && tttLargeFiber50Block6Chunk1RowCheck 9
    && tttLargeFiber50Block6Chunk1RowCheck 10
    && tttLargeFiber50Block6Chunk1RowCheck 11
    && tttLargeFiber50Block6Chunk1RowCheck 12
    && tttLargeFiber50Block6Chunk1RowCheck 13
    && tttLargeFiber50Block6Chunk1RowCheck 14
    && tttLargeFiber50Block6Chunk1RowCheck 15

theorem tttLargeFiber50Block6Chunk1RowsAudit_ok :
    tttLargeFiber50Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber50Block6Chunk1RowsAudit,
    tttLargeFiber50Block6Chunk1Row_0_ok,
    tttLargeFiber50Block6Chunk1Row_1_ok,
    tttLargeFiber50Block6Chunk1Row_2_ok,
    tttLargeFiber50Block6Chunk1Row_3_ok,
    tttLargeFiber50Block6Chunk1Row_4_ok,
    tttLargeFiber50Block6Chunk1Row_5_ok,
    tttLargeFiber50Block6Chunk1Row_6_ok,
    tttLargeFiber50Block6Chunk1Row_7_ok,
    tttLargeFiber50Block6Chunk1Row_8_ok,
    tttLargeFiber50Block6Chunk1Row_9_ok,
    tttLargeFiber50Block6Chunk1Row_10_ok,
    tttLargeFiber50Block6Chunk1Row_11_ok,
    tttLargeFiber50Block6Chunk1Row_12_ok,
    tttLargeFiber50Block6Chunk1Row_13_ok,
    tttLargeFiber50Block6Chunk1Row_14_ok,
    tttLargeFiber50Block6Chunk1Row_15_ok]

def tttLargeFiber50Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber50Block6Chunk1ParentMapCheck 0
    && tttLargeFiber50Block6Chunk1ParentMapCheck 1
    && tttLargeFiber50Block6Chunk1ParentMapCheck 2
    && tttLargeFiber50Block6Chunk1ParentMapCheck 3
    && tttLargeFiber50Block6Chunk1ParentMapCheck 4
    && tttLargeFiber50Block6Chunk1ParentMapCheck 5
    && tttLargeFiber50Block6Chunk1ParentMapCheck 6
    && tttLargeFiber50Block6Chunk1ParentMapCheck 7
    && tttLargeFiber50Block6Chunk1ParentMapCheck 8
    && tttLargeFiber50Block6Chunk1ParentMapCheck 9
    && tttLargeFiber50Block6Chunk1ParentMapCheck 10
    && tttLargeFiber50Block6Chunk1ParentMapCheck 11
    && tttLargeFiber50Block6Chunk1ParentMapCheck 12
    && tttLargeFiber50Block6Chunk1ParentMapCheck 13
    && tttLargeFiber50Block6Chunk1ParentMapCheck 14
    && tttLargeFiber50Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber50Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber50Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber50Block6Chunk1ParentMapAudit,
    tttLargeFiber50Block6Chunk1ParentMap_0_ok,
    tttLargeFiber50Block6Chunk1ParentMap_1_ok,
    tttLargeFiber50Block6Chunk1ParentMap_2_ok,
    tttLargeFiber50Block6Chunk1ParentMap_3_ok,
    tttLargeFiber50Block6Chunk1ParentMap_4_ok,
    tttLargeFiber50Block6Chunk1ParentMap_5_ok,
    tttLargeFiber50Block6Chunk1ParentMap_6_ok,
    tttLargeFiber50Block6Chunk1ParentMap_7_ok,
    tttLargeFiber50Block6Chunk1ParentMap_8_ok,
    tttLargeFiber50Block6Chunk1ParentMap_9_ok,
    tttLargeFiber50Block6Chunk1ParentMap_10_ok,
    tttLargeFiber50Block6Chunk1ParentMap_11_ok,
    tttLargeFiber50Block6Chunk1ParentMap_12_ok,
    tttLargeFiber50Block6Chunk1ParentMap_13_ok,
    tttLargeFiber50Block6Chunk1ParentMap_14_ok,
    tttLargeFiber50Block6Chunk1ParentMap_15_ok]

def tttLargeFiber50Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber50Block6Chunk1ParentPathCheck 0
    && tttLargeFiber50Block6Chunk1ParentPathCheck 1
    && tttLargeFiber50Block6Chunk1ParentPathCheck 2
    && tttLargeFiber50Block6Chunk1ParentPathCheck 3
    && tttLargeFiber50Block6Chunk1ParentPathCheck 4
    && tttLargeFiber50Block6Chunk1ParentPathCheck 5
    && tttLargeFiber50Block6Chunk1ParentPathCheck 6
    && tttLargeFiber50Block6Chunk1ParentPathCheck 7
    && tttLargeFiber50Block6Chunk1ParentPathCheck 8
    && tttLargeFiber50Block6Chunk1ParentPathCheck 9
    && tttLargeFiber50Block6Chunk1ParentPathCheck 10
    && tttLargeFiber50Block6Chunk1ParentPathCheck 11
    && tttLargeFiber50Block6Chunk1ParentPathCheck 12
    && tttLargeFiber50Block6Chunk1ParentPathCheck 13
    && tttLargeFiber50Block6Chunk1ParentPathCheck 14
    && tttLargeFiber50Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber50Block6Chunk1ParentsAudit_ok :
    tttLargeFiber50Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber50Block6Chunk1ParentsAudit,
    tttLargeFiber50Block6Chunk1ParentPath_0_ok,
    tttLargeFiber50Block6Chunk1ParentPath_1_ok,
    tttLargeFiber50Block6Chunk1ParentPath_2_ok,
    tttLargeFiber50Block6Chunk1ParentPath_3_ok,
    tttLargeFiber50Block6Chunk1ParentPath_4_ok,
    tttLargeFiber50Block6Chunk1ParentPath_5_ok,
    tttLargeFiber50Block6Chunk1ParentPath_6_ok,
    tttLargeFiber50Block6Chunk1ParentPath_7_ok,
    tttLargeFiber50Block6Chunk1ParentPath_8_ok,
    tttLargeFiber50Block6Chunk1ParentPath_9_ok,
    tttLargeFiber50Block6Chunk1ParentPath_10_ok,
    tttLargeFiber50Block6Chunk1ParentPath_11_ok,
    tttLargeFiber50Block6Chunk1ParentPath_12_ok,
    tttLargeFiber50Block6Chunk1ParentPath_13_ok,
    tttLargeFiber50Block6Chunk1ParentPath_14_ok,
    tttLargeFiber50Block6Chunk1ParentPath_15_ok]

def tttLargeFiber50Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block6Chunk1SourcesCheck &&
    tttLargeFiber50Block6Chunk1RowsAudit &&
    tttLargeFiber50Block6Chunk1ParentMapAudit &&
    tttLargeFiber50Block6Chunk1ParentsAudit

theorem tttLargeFiber50Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber50Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block6Chunk1SourcesCheck_ok,
    tttLargeFiber50Block6Chunk1RowsAudit_ok,
    tttLargeFiber50Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber50Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
