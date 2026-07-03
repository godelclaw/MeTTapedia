import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block1Chunk2Sources : List Nat :=
  [   5008, 5009, 5010, 5011, 5012, 5013, 5014, 5015,
   5016, 5017, 5018, 5019, 5020, 5021, 5022, 5023]

def tttLargeFiber44Row96 : TripleComponentParentRow :=
  tripleRow 5008 4944 149 172 132 148 164 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row97 : TripleComponentParentRow :=
  tripleRow 5009 4945 149 172 133 148 164 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row98 : TripleComponentParentRow :=
  tripleRow 5010 4946 149 172 134 148 164 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row99 : TripleComponentParentRow :=
  tripleRow 5011 4947 149 172 135 148 164 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row100 : TripleComponentParentRow :=
  tripleRow 5012 4948 149 172 180 148 164 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row101 : TripleComponentParentRow :=
  tripleRow 5013 4949 149 172 181 148 164 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row102 : TripleComponentParentRow :=
  tripleRow 5014 4950 149 172 182 148 164 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row103 : TripleComponentParentRow :=
  tripleRow 5015 4951 149 172 183 148 164 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row104 : TripleComponentParentRow :=
  tripleRow 5016 4952 149 173 140 148 165 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row105 : TripleComponentParentRow :=
  tripleRow 5017 4953 149 173 141 148 165 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row106 : TripleComponentParentRow :=
  tripleRow 5018 4954 149 173 142 148 165 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row107 : TripleComponentParentRow :=
  tripleRow 5019 4955 149 173 143 148 165 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row108 : TripleComponentParentRow :=
  tripleRow 5020 4956 149 173 188 148 165 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row109 : TripleComponentParentRow :=
  tripleRow 5021 4957 149 173 189 148 165 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row110 : TripleComponentParentRow :=
  tripleRow 5022 4958 149 173 190 148 165 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row111 : TripleComponentParentRow :=
  tripleRow 5023 4959 149 173 191 148 165 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row96
  , tttLargeFiber44Row97
  , tttLargeFiber44Row98
  , tttLargeFiber44Row99
  , tttLargeFiber44Row100
  , tttLargeFiber44Row101
  , tttLargeFiber44Row102
  , tttLargeFiber44Row103
  , tttLargeFiber44Row104
  , tttLargeFiber44Row105
  , tttLargeFiber44Row106
  , tttLargeFiber44Row107
  , tttLargeFiber44Row108
  , tttLargeFiber44Row109
  , tttLargeFiber44Row110
  , tttLargeFiber44Row111
  ]

def tttLargeFiber44Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber44Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber44Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber44Block1Chunk2Sources

theorem tttLargeFiber44Block1Chunk2SourcesCheck_ok :
    tttLargeFiber44Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber44Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block1Chunk2RowValid
    (listGetD tttLargeFiber44Block1Chunk2Rows i default)

def tttLargeFiber44Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block1Chunk2Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block1Chunk2Sources 0 0 == 5008
      && tttLargeFiber44ParentOf 5008 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block1Chunk2Sources 1 0 == 5009
      && tttLargeFiber44ParentOf 5009 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block1Chunk2Sources 2 0 == 5010
      && tttLargeFiber44ParentOf 5010 == 4946
      && tttLargeFiber44ParentOf 4946 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block1Chunk2Sources 3 0 == 5011
      && tttLargeFiber44ParentOf 5011 == 4947
      && tttLargeFiber44ParentOf 4947 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block1Chunk2Sources 4 0 == 5012
      && tttLargeFiber44ParentOf 5012 == 4948
      && tttLargeFiber44ParentOf 4948 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block1Chunk2Sources 5 0 == 5013
      && tttLargeFiber44ParentOf 5013 == 4949
      && tttLargeFiber44ParentOf 4949 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block1Chunk2Sources 6 0 == 5014
      && tttLargeFiber44ParentOf 5014 == 4950
      && tttLargeFiber44ParentOf 4950 == 4918
      && tttLargeFiber44ParentOf 4918 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block1Chunk2Sources 7 0 == 5015
      && tttLargeFiber44ParentOf 5015 == 4951
      && tttLargeFiber44ParentOf 4951 == 4919
      && tttLargeFiber44ParentOf 4919 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block1Chunk2Sources 8 0 == 5016
      && tttLargeFiber44ParentOf 5016 == 4952
      && tttLargeFiber44ParentOf 4952 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block1Chunk2Sources 9 0 == 5017
      && tttLargeFiber44ParentOf 5017 == 4953
      && tttLargeFiber44ParentOf 4953 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block1Chunk2Sources 10 0 == 5018
      && tttLargeFiber44ParentOf 5018 == 4954
      && tttLargeFiber44ParentOf 4954 == 4922
      && tttLargeFiber44ParentOf 4922 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block1Chunk2Sources 11 0 == 5019
      && tttLargeFiber44ParentOf 5019 == 4955
      && tttLargeFiber44ParentOf 4955 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block1Chunk2Sources 12 0 == 5020
      && tttLargeFiber44ParentOf 5020 == 4956
      && tttLargeFiber44ParentOf 4956 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block1Chunk2Sources 13 0 == 5021
      && tttLargeFiber44ParentOf 5021 == 4957
      && tttLargeFiber44ParentOf 4957 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block1Chunk2Sources 14 0 == 5022
      && tttLargeFiber44ParentOf 5022 == 4958
      && tttLargeFiber44ParentOf 4958 == 4926
      && tttLargeFiber44ParentOf 4926 == 4918
      && tttLargeFiber44ParentOf 4918 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block1Chunk2Sources 15 0 == 5023
      && tttLargeFiber44ParentOf 5023 == 4959
      && tttLargeFiber44ParentOf 4959 == 4927
      && tttLargeFiber44ParentOf 4927 == 4919
      && tttLargeFiber44ParentOf 4919 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block1Chunk2Row_0_ok :
    tttLargeFiber44Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_1_ok :
    tttLargeFiber44Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_2_ok :
    tttLargeFiber44Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_3_ok :
    tttLargeFiber44Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_4_ok :
    tttLargeFiber44Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_5_ok :
    tttLargeFiber44Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_6_ok :
    tttLargeFiber44Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_7_ok :
    tttLargeFiber44Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_8_ok :
    tttLargeFiber44Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_9_ok :
    tttLargeFiber44Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_10_ok :
    tttLargeFiber44Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_11_ok :
    tttLargeFiber44Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_12_ok :
    tttLargeFiber44Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_13_ok :
    tttLargeFiber44Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_14_ok :
    tttLargeFiber44Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2Row_15_ok :
    tttLargeFiber44Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_0_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_1_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_2_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_3_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_4_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_5_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_6_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_7_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_8_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_9_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_10_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_11_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_12_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_13_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_14_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentMap_15_ok :
    tttLargeFiber44Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_0_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_1_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_2_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_3_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_4_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_5_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_6_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_7_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_8_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_9_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_10_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_11_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_12_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_13_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_14_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk2ParentPath_15_ok :
    tttLargeFiber44Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber44Block1Chunk2RowCheck 0
    && tttLargeFiber44Block1Chunk2RowCheck 1
    && tttLargeFiber44Block1Chunk2RowCheck 2
    && tttLargeFiber44Block1Chunk2RowCheck 3
    && tttLargeFiber44Block1Chunk2RowCheck 4
    && tttLargeFiber44Block1Chunk2RowCheck 5
    && tttLargeFiber44Block1Chunk2RowCheck 6
    && tttLargeFiber44Block1Chunk2RowCheck 7
    && tttLargeFiber44Block1Chunk2RowCheck 8
    && tttLargeFiber44Block1Chunk2RowCheck 9
    && tttLargeFiber44Block1Chunk2RowCheck 10
    && tttLargeFiber44Block1Chunk2RowCheck 11
    && tttLargeFiber44Block1Chunk2RowCheck 12
    && tttLargeFiber44Block1Chunk2RowCheck 13
    && tttLargeFiber44Block1Chunk2RowCheck 14
    && tttLargeFiber44Block1Chunk2RowCheck 15

theorem tttLargeFiber44Block1Chunk2RowsAudit_ok :
    tttLargeFiber44Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber44Block1Chunk2RowsAudit,
    tttLargeFiber44Block1Chunk2Row_0_ok,
    tttLargeFiber44Block1Chunk2Row_1_ok,
    tttLargeFiber44Block1Chunk2Row_2_ok,
    tttLargeFiber44Block1Chunk2Row_3_ok,
    tttLargeFiber44Block1Chunk2Row_4_ok,
    tttLargeFiber44Block1Chunk2Row_5_ok,
    tttLargeFiber44Block1Chunk2Row_6_ok,
    tttLargeFiber44Block1Chunk2Row_7_ok,
    tttLargeFiber44Block1Chunk2Row_8_ok,
    tttLargeFiber44Block1Chunk2Row_9_ok,
    tttLargeFiber44Block1Chunk2Row_10_ok,
    tttLargeFiber44Block1Chunk2Row_11_ok,
    tttLargeFiber44Block1Chunk2Row_12_ok,
    tttLargeFiber44Block1Chunk2Row_13_ok,
    tttLargeFiber44Block1Chunk2Row_14_ok,
    tttLargeFiber44Block1Chunk2Row_15_ok]

def tttLargeFiber44Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber44Block1Chunk2ParentMapCheck 0
    && tttLargeFiber44Block1Chunk2ParentMapCheck 1
    && tttLargeFiber44Block1Chunk2ParentMapCheck 2
    && tttLargeFiber44Block1Chunk2ParentMapCheck 3
    && tttLargeFiber44Block1Chunk2ParentMapCheck 4
    && tttLargeFiber44Block1Chunk2ParentMapCheck 5
    && tttLargeFiber44Block1Chunk2ParentMapCheck 6
    && tttLargeFiber44Block1Chunk2ParentMapCheck 7
    && tttLargeFiber44Block1Chunk2ParentMapCheck 8
    && tttLargeFiber44Block1Chunk2ParentMapCheck 9
    && tttLargeFiber44Block1Chunk2ParentMapCheck 10
    && tttLargeFiber44Block1Chunk2ParentMapCheck 11
    && tttLargeFiber44Block1Chunk2ParentMapCheck 12
    && tttLargeFiber44Block1Chunk2ParentMapCheck 13
    && tttLargeFiber44Block1Chunk2ParentMapCheck 14
    && tttLargeFiber44Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber44Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber44Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber44Block1Chunk2ParentMapAudit,
    tttLargeFiber44Block1Chunk2ParentMap_0_ok,
    tttLargeFiber44Block1Chunk2ParentMap_1_ok,
    tttLargeFiber44Block1Chunk2ParentMap_2_ok,
    tttLargeFiber44Block1Chunk2ParentMap_3_ok,
    tttLargeFiber44Block1Chunk2ParentMap_4_ok,
    tttLargeFiber44Block1Chunk2ParentMap_5_ok,
    tttLargeFiber44Block1Chunk2ParentMap_6_ok,
    tttLargeFiber44Block1Chunk2ParentMap_7_ok,
    tttLargeFiber44Block1Chunk2ParentMap_8_ok,
    tttLargeFiber44Block1Chunk2ParentMap_9_ok,
    tttLargeFiber44Block1Chunk2ParentMap_10_ok,
    tttLargeFiber44Block1Chunk2ParentMap_11_ok,
    tttLargeFiber44Block1Chunk2ParentMap_12_ok,
    tttLargeFiber44Block1Chunk2ParentMap_13_ok,
    tttLargeFiber44Block1Chunk2ParentMap_14_ok,
    tttLargeFiber44Block1Chunk2ParentMap_15_ok]

def tttLargeFiber44Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber44Block1Chunk2ParentPathCheck 0
    && tttLargeFiber44Block1Chunk2ParentPathCheck 1
    && tttLargeFiber44Block1Chunk2ParentPathCheck 2
    && tttLargeFiber44Block1Chunk2ParentPathCheck 3
    && tttLargeFiber44Block1Chunk2ParentPathCheck 4
    && tttLargeFiber44Block1Chunk2ParentPathCheck 5
    && tttLargeFiber44Block1Chunk2ParentPathCheck 6
    && tttLargeFiber44Block1Chunk2ParentPathCheck 7
    && tttLargeFiber44Block1Chunk2ParentPathCheck 8
    && tttLargeFiber44Block1Chunk2ParentPathCheck 9
    && tttLargeFiber44Block1Chunk2ParentPathCheck 10
    && tttLargeFiber44Block1Chunk2ParentPathCheck 11
    && tttLargeFiber44Block1Chunk2ParentPathCheck 12
    && tttLargeFiber44Block1Chunk2ParentPathCheck 13
    && tttLargeFiber44Block1Chunk2ParentPathCheck 14
    && tttLargeFiber44Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber44Block1Chunk2ParentsAudit_ok :
    tttLargeFiber44Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber44Block1Chunk2ParentsAudit,
    tttLargeFiber44Block1Chunk2ParentPath_0_ok,
    tttLargeFiber44Block1Chunk2ParentPath_1_ok,
    tttLargeFiber44Block1Chunk2ParentPath_2_ok,
    tttLargeFiber44Block1Chunk2ParentPath_3_ok,
    tttLargeFiber44Block1Chunk2ParentPath_4_ok,
    tttLargeFiber44Block1Chunk2ParentPath_5_ok,
    tttLargeFiber44Block1Chunk2ParentPath_6_ok,
    tttLargeFiber44Block1Chunk2ParentPath_7_ok,
    tttLargeFiber44Block1Chunk2ParentPath_8_ok,
    tttLargeFiber44Block1Chunk2ParentPath_9_ok,
    tttLargeFiber44Block1Chunk2ParentPath_10_ok,
    tttLargeFiber44Block1Chunk2ParentPath_11_ok,
    tttLargeFiber44Block1Chunk2ParentPath_12_ok,
    tttLargeFiber44Block1Chunk2ParentPath_13_ok,
    tttLargeFiber44Block1Chunk2ParentPath_14_ok,
    tttLargeFiber44Block1Chunk2ParentPath_15_ok]

def tttLargeFiber44Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block1Chunk2SourcesCheck &&
    tttLargeFiber44Block1Chunk2RowsAudit &&
    tttLargeFiber44Block1Chunk2ParentMapAudit &&
    tttLargeFiber44Block1Chunk2ParentsAudit

theorem tttLargeFiber44Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber44Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block1Chunk2SourcesCheck_ok,
    tttLargeFiber44Block1Chunk2RowsAudit_ok,
    tttLargeFiber44Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber44Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
