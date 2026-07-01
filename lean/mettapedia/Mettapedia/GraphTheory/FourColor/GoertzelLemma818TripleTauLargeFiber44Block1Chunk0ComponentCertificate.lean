import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block1Chunk0Sources : List Nat :=
  [   4976, 4977, 4978, 4979, 4980, 4981, 4982, 4983,
   4984, 4985, 4986, 4987, 4988, 4989, 4990, 4991]

def tttLargeFiber44Row64 : TripleComponentParentRow :=
  tripleRow 4976 4912 149 156 148 148 148 148
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row65 : TripleComponentParentRow :=
  tripleRow 4977 4913 149 156 149 148 148 149
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row66 : TripleComponentParentRow :=
  tripleRow 4978 4914 149 156 150 148 148 150
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row67 : TripleComponentParentRow :=
  tripleRow 4979 4915 149 156 151 148 148 151
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row68 : TripleComponentParentRow :=
  tripleRow 4980 4916 149 156 164 148 148 164
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row69 : TripleComponentParentRow :=
  tripleRow 4981 4917 149 156 165 148 148 165
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row70 : TripleComponentParentRow :=
  tripleRow 4982 4918 149 156 166 148 148 166
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row71 : TripleComponentParentRow :=
  tripleRow 4983 4919 149 156 167 148 148 167
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row72 : TripleComponentParentRow :=
  tripleRow 4984 4920 149 157 156 148 149 156
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row73 : TripleComponentParentRow :=
  tripleRow 4985 4921 149 157 157 148 149 157
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row74 : TripleComponentParentRow :=
  tripleRow 4986 4922 149 157 158 148 149 158
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row75 : TripleComponentParentRow :=
  tripleRow 4987 4923 149 157 159 148 149 159
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row76 : TripleComponentParentRow :=
  tripleRow 4988 4924 149 157 172 148 149 172
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row77 : TripleComponentParentRow :=
  tripleRow 4989 4925 149 157 173 148 149 173
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row78 : TripleComponentParentRow :=
  tripleRow 4990 4926 149 157 174 148 149 174
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row79 : TripleComponentParentRow :=
  tripleRow 4991 4927 149 157 175 148 149 175
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row64
  , tttLargeFiber44Row65
  , tttLargeFiber44Row66
  , tttLargeFiber44Row67
  , tttLargeFiber44Row68
  , tttLargeFiber44Row69
  , tttLargeFiber44Row70
  , tttLargeFiber44Row71
  , tttLargeFiber44Row72
  , tttLargeFiber44Row73
  , tttLargeFiber44Row74
  , tttLargeFiber44Row75
  , tttLargeFiber44Row76
  , tttLargeFiber44Row77
  , tttLargeFiber44Row78
  , tttLargeFiber44Row79
  ]

def tttLargeFiber44Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber44Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber44Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber44Block1Chunk0Sources

theorem tttLargeFiber44Block1Chunk0SourcesCheck_ok :
    tttLargeFiber44Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber44Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block1Chunk0RowValid
    (listGetD tttLargeFiber44Block1Chunk0Rows i default)

def tttLargeFiber44Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block1Chunk0Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block1Chunk0Sources 0 0 == 4976
      && tttLargeFiber44ParentOf 4976 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (1 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block1Chunk0Sources 1 0 == 4977
      && tttLargeFiber44ParentOf 4977 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block1Chunk0Sources 2 0 == 4978
      && tttLargeFiber44ParentOf 4978 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block1Chunk0Sources 3 0 == 4979
      && tttLargeFiber44ParentOf 4979 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block1Chunk0Sources 4 0 == 4980
      && tttLargeFiber44ParentOf 4980 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block1Chunk0Sources 5 0 == 4981
      && tttLargeFiber44ParentOf 4981 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block1Chunk0Sources 6 0 == 4982
      && tttLargeFiber44ParentOf 4982 == 4918
      && tttLargeFiber44ParentOf 4918 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block1Chunk0Sources 7 0 == 4983
      && tttLargeFiber44ParentOf 4983 == 4919
      && tttLargeFiber44ParentOf 4919 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block1Chunk0Sources 8 0 == 4984
      && tttLargeFiber44ParentOf 4984 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block1Chunk0Sources 9 0 == 4985
      && tttLargeFiber44ParentOf 4985 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block1Chunk0Sources 10 0 == 4986
      && tttLargeFiber44ParentOf 4986 == 4922
      && tttLargeFiber44ParentOf 4922 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block1Chunk0Sources 11 0 == 4987
      && tttLargeFiber44ParentOf 4987 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block1Chunk0Sources 12 0 == 4988
      && tttLargeFiber44ParentOf 4988 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block1Chunk0Sources 13 0 == 4989
      && tttLargeFiber44ParentOf 4989 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block1Chunk0Sources 14 0 == 4990
      && tttLargeFiber44ParentOf 4990 == 4926
      && tttLargeFiber44ParentOf 4926 == 4918
      && tttLargeFiber44ParentOf 4918 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block1Chunk0Sources 15 0 == 4991
      && tttLargeFiber44ParentOf 4991 == 4927
      && tttLargeFiber44ParentOf 4927 == 4919
      && tttLargeFiber44ParentOf 4919 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block1Chunk0Row_0_ok :
    tttLargeFiber44Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_1_ok :
    tttLargeFiber44Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_2_ok :
    tttLargeFiber44Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_3_ok :
    tttLargeFiber44Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_4_ok :
    tttLargeFiber44Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_5_ok :
    tttLargeFiber44Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_6_ok :
    tttLargeFiber44Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_7_ok :
    tttLargeFiber44Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_8_ok :
    tttLargeFiber44Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_9_ok :
    tttLargeFiber44Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_10_ok :
    tttLargeFiber44Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_11_ok :
    tttLargeFiber44Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_12_ok :
    tttLargeFiber44Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_13_ok :
    tttLargeFiber44Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_14_ok :
    tttLargeFiber44Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0Row_15_ok :
    tttLargeFiber44Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_0_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_1_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_2_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_3_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_4_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_5_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_6_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_7_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_8_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_9_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_10_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_11_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_12_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_13_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_14_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentMap_15_ok :
    tttLargeFiber44Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_0_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_1_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_2_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_3_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_4_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_5_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_6_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_7_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_8_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_9_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_10_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_11_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_12_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_13_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_14_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk0ParentPath_15_ok :
    tttLargeFiber44Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber44Block1Chunk0RowCheck 0
    && tttLargeFiber44Block1Chunk0RowCheck 1
    && tttLargeFiber44Block1Chunk0RowCheck 2
    && tttLargeFiber44Block1Chunk0RowCheck 3
    && tttLargeFiber44Block1Chunk0RowCheck 4
    && tttLargeFiber44Block1Chunk0RowCheck 5
    && tttLargeFiber44Block1Chunk0RowCheck 6
    && tttLargeFiber44Block1Chunk0RowCheck 7
    && tttLargeFiber44Block1Chunk0RowCheck 8
    && tttLargeFiber44Block1Chunk0RowCheck 9
    && tttLargeFiber44Block1Chunk0RowCheck 10
    && tttLargeFiber44Block1Chunk0RowCheck 11
    && tttLargeFiber44Block1Chunk0RowCheck 12
    && tttLargeFiber44Block1Chunk0RowCheck 13
    && tttLargeFiber44Block1Chunk0RowCheck 14
    && tttLargeFiber44Block1Chunk0RowCheck 15

theorem tttLargeFiber44Block1Chunk0RowsAudit_ok :
    tttLargeFiber44Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber44Block1Chunk0RowsAudit,
    tttLargeFiber44Block1Chunk0Row_0_ok,
    tttLargeFiber44Block1Chunk0Row_1_ok,
    tttLargeFiber44Block1Chunk0Row_2_ok,
    tttLargeFiber44Block1Chunk0Row_3_ok,
    tttLargeFiber44Block1Chunk0Row_4_ok,
    tttLargeFiber44Block1Chunk0Row_5_ok,
    tttLargeFiber44Block1Chunk0Row_6_ok,
    tttLargeFiber44Block1Chunk0Row_7_ok,
    tttLargeFiber44Block1Chunk0Row_8_ok,
    tttLargeFiber44Block1Chunk0Row_9_ok,
    tttLargeFiber44Block1Chunk0Row_10_ok,
    tttLargeFiber44Block1Chunk0Row_11_ok,
    tttLargeFiber44Block1Chunk0Row_12_ok,
    tttLargeFiber44Block1Chunk0Row_13_ok,
    tttLargeFiber44Block1Chunk0Row_14_ok,
    tttLargeFiber44Block1Chunk0Row_15_ok]

def tttLargeFiber44Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber44Block1Chunk0ParentMapCheck 0
    && tttLargeFiber44Block1Chunk0ParentMapCheck 1
    && tttLargeFiber44Block1Chunk0ParentMapCheck 2
    && tttLargeFiber44Block1Chunk0ParentMapCheck 3
    && tttLargeFiber44Block1Chunk0ParentMapCheck 4
    && tttLargeFiber44Block1Chunk0ParentMapCheck 5
    && tttLargeFiber44Block1Chunk0ParentMapCheck 6
    && tttLargeFiber44Block1Chunk0ParentMapCheck 7
    && tttLargeFiber44Block1Chunk0ParentMapCheck 8
    && tttLargeFiber44Block1Chunk0ParentMapCheck 9
    && tttLargeFiber44Block1Chunk0ParentMapCheck 10
    && tttLargeFiber44Block1Chunk0ParentMapCheck 11
    && tttLargeFiber44Block1Chunk0ParentMapCheck 12
    && tttLargeFiber44Block1Chunk0ParentMapCheck 13
    && tttLargeFiber44Block1Chunk0ParentMapCheck 14
    && tttLargeFiber44Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber44Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber44Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber44Block1Chunk0ParentMapAudit,
    tttLargeFiber44Block1Chunk0ParentMap_0_ok,
    tttLargeFiber44Block1Chunk0ParentMap_1_ok,
    tttLargeFiber44Block1Chunk0ParentMap_2_ok,
    tttLargeFiber44Block1Chunk0ParentMap_3_ok,
    tttLargeFiber44Block1Chunk0ParentMap_4_ok,
    tttLargeFiber44Block1Chunk0ParentMap_5_ok,
    tttLargeFiber44Block1Chunk0ParentMap_6_ok,
    tttLargeFiber44Block1Chunk0ParentMap_7_ok,
    tttLargeFiber44Block1Chunk0ParentMap_8_ok,
    tttLargeFiber44Block1Chunk0ParentMap_9_ok,
    tttLargeFiber44Block1Chunk0ParentMap_10_ok,
    tttLargeFiber44Block1Chunk0ParentMap_11_ok,
    tttLargeFiber44Block1Chunk0ParentMap_12_ok,
    tttLargeFiber44Block1Chunk0ParentMap_13_ok,
    tttLargeFiber44Block1Chunk0ParentMap_14_ok,
    tttLargeFiber44Block1Chunk0ParentMap_15_ok]

def tttLargeFiber44Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber44Block1Chunk0ParentPathCheck 0
    && tttLargeFiber44Block1Chunk0ParentPathCheck 1
    && tttLargeFiber44Block1Chunk0ParentPathCheck 2
    && tttLargeFiber44Block1Chunk0ParentPathCheck 3
    && tttLargeFiber44Block1Chunk0ParentPathCheck 4
    && tttLargeFiber44Block1Chunk0ParentPathCheck 5
    && tttLargeFiber44Block1Chunk0ParentPathCheck 6
    && tttLargeFiber44Block1Chunk0ParentPathCheck 7
    && tttLargeFiber44Block1Chunk0ParentPathCheck 8
    && tttLargeFiber44Block1Chunk0ParentPathCheck 9
    && tttLargeFiber44Block1Chunk0ParentPathCheck 10
    && tttLargeFiber44Block1Chunk0ParentPathCheck 11
    && tttLargeFiber44Block1Chunk0ParentPathCheck 12
    && tttLargeFiber44Block1Chunk0ParentPathCheck 13
    && tttLargeFiber44Block1Chunk0ParentPathCheck 14
    && tttLargeFiber44Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber44Block1Chunk0ParentsAudit_ok :
    tttLargeFiber44Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber44Block1Chunk0ParentsAudit,
    tttLargeFiber44Block1Chunk0ParentPath_0_ok,
    tttLargeFiber44Block1Chunk0ParentPath_1_ok,
    tttLargeFiber44Block1Chunk0ParentPath_2_ok,
    tttLargeFiber44Block1Chunk0ParentPath_3_ok,
    tttLargeFiber44Block1Chunk0ParentPath_4_ok,
    tttLargeFiber44Block1Chunk0ParentPath_5_ok,
    tttLargeFiber44Block1Chunk0ParentPath_6_ok,
    tttLargeFiber44Block1Chunk0ParentPath_7_ok,
    tttLargeFiber44Block1Chunk0ParentPath_8_ok,
    tttLargeFiber44Block1Chunk0ParentPath_9_ok,
    tttLargeFiber44Block1Chunk0ParentPath_10_ok,
    tttLargeFiber44Block1Chunk0ParentPath_11_ok,
    tttLargeFiber44Block1Chunk0ParentPath_12_ok,
    tttLargeFiber44Block1Chunk0ParentPath_13_ok,
    tttLargeFiber44Block1Chunk0ParentPath_14_ok,
    tttLargeFiber44Block1Chunk0ParentPath_15_ok]

def tttLargeFiber44Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block1Chunk0SourcesCheck &&
    tttLargeFiber44Block1Chunk0RowsAudit &&
    tttLargeFiber44Block1Chunk0ParentMapAudit &&
    tttLargeFiber44Block1Chunk0ParentsAudit

theorem tttLargeFiber44Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber44Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block1Chunk0SourcesCheck_ok,
    tttLargeFiber44Block1Chunk0RowsAudit_ok,
    tttLargeFiber44Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber44Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
