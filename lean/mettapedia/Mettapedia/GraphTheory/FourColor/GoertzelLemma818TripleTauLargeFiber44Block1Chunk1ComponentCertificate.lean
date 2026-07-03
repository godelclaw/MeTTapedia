import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block1Chunk1Sources : List Nat :=
  [   4992, 4993, 4994, 4995, 4996, 4997, 4998, 4999,
   5000, 5001, 5002, 5003, 5004, 5005, 5006, 5007]

def tttLargeFiber44Row80 : TripleComponentParentRow :=
  tripleRow 4992 4928 149 158 0 148 150 0
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row81 : TripleComponentParentRow :=
  tripleRow 4993 4929 149 158 1 148 150 1
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row82 : TripleComponentParentRow :=
  tripleRow 4994 4930 149 158 2 148 150 2
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row83 : TripleComponentParentRow :=
  tripleRow 4995 4931 149 158 3 148 150 3
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row84 : TripleComponentParentRow :=
  tripleRow 4996 4932 149 158 48 148 150 48
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row85 : TripleComponentParentRow :=
  tripleRow 4997 4933 149 158 49 148 150 49
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row86 : TripleComponentParentRow :=
  tripleRow 4998 4934 149 158 50 148 150 50
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row87 : TripleComponentParentRow :=
  tripleRow 4999 4935 149 158 51 148 150 51
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row88 : TripleComponentParentRow :=
  tripleRow 5000 4936 149 159 8 148 151 8
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row89 : TripleComponentParentRow :=
  tripleRow 5001 4937 149 159 9 148 151 9
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row90 : TripleComponentParentRow :=
  tripleRow 5002 4938 149 159 10 148 151 10
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row91 : TripleComponentParentRow :=
  tripleRow 5003 4939 149 159 11 148 151 11
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row92 : TripleComponentParentRow :=
  tripleRow 5004 4940 149 159 56 148 151 56
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row93 : TripleComponentParentRow :=
  tripleRow 5005 4941 149 159 57 148 151 57
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row94 : TripleComponentParentRow :=
  tripleRow 5006 4942 149 159 58 148 151 58
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row95 : TripleComponentParentRow :=
  tripleRow 5007 4943 149 159 59 148 151 59
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row80
  , tttLargeFiber44Row81
  , tttLargeFiber44Row82
  , tttLargeFiber44Row83
  , tttLargeFiber44Row84
  , tttLargeFiber44Row85
  , tttLargeFiber44Row86
  , tttLargeFiber44Row87
  , tttLargeFiber44Row88
  , tttLargeFiber44Row89
  , tttLargeFiber44Row90
  , tttLargeFiber44Row91
  , tttLargeFiber44Row92
  , tttLargeFiber44Row93
  , tttLargeFiber44Row94
  , tttLargeFiber44Row95
  ]

def tttLargeFiber44Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber44Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber44Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber44Block1Chunk1Sources

theorem tttLargeFiber44Block1Chunk1SourcesCheck_ok :
    tttLargeFiber44Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber44Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block1Chunk1RowValid
    (listGetD tttLargeFiber44Block1Chunk1Rows i default)

def tttLargeFiber44Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block1Chunk1Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block1Chunk1Sources 0 0 == 4992
      && tttLargeFiber44ParentOf 4992 == 4928
      && tttLargeFiber44ParentOf 4928 == 4932
      && tttLargeFiber44ParentOf 4932 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block1Chunk1Sources 1 0 == 4993
      && tttLargeFiber44ParentOf 4993 == 4929
      && tttLargeFiber44ParentOf 4929 == 4933
      && tttLargeFiber44ParentOf 4933 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block1Chunk1Sources 2 0 == 4994
      && tttLargeFiber44ParentOf 4994 == 4930
      && tttLargeFiber44ParentOf 4930 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block1Chunk1Sources 3 0 == 4995
      && tttLargeFiber44ParentOf 4995 == 4931
      && tttLargeFiber44ParentOf 4931 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block1Chunk1Sources 4 0 == 4996
      && tttLargeFiber44ParentOf 4996 == 4932
      && tttLargeFiber44ParentOf 4932 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block1Chunk1Sources 5 0 == 4997
      && tttLargeFiber44ParentOf 4997 == 4933
      && tttLargeFiber44ParentOf 4933 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block1Chunk1Sources 6 0 == 4998
      && tttLargeFiber44ParentOf 4998 == 4934
      && tttLargeFiber44ParentOf 4934 == 4922
      && tttLargeFiber44ParentOf 4922 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block1Chunk1Sources 7 0 == 4999
      && tttLargeFiber44ParentOf 4999 == 4935
      && tttLargeFiber44ParentOf 4935 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block1Chunk1Sources 8 0 == 5000
      && tttLargeFiber44ParentOf 5000 == 4936
      && tttLargeFiber44ParentOf 4936 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block1Chunk1Sources 9 0 == 5001
      && tttLargeFiber44ParentOf 5001 == 4937
      && tttLargeFiber44ParentOf 4937 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block1Chunk1Sources 10 0 == 5002
      && tttLargeFiber44ParentOf 5002 == 4938
      && tttLargeFiber44ParentOf 4938 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block1Chunk1Sources 11 0 == 5003
      && tttLargeFiber44ParentOf 5003 == 4939
      && tttLargeFiber44ParentOf 4939 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block1Chunk1Sources 12 0 == 5004
      && tttLargeFiber44ParentOf 5004 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block1Chunk1Sources 13 0 == 5005
      && tttLargeFiber44ParentOf 5005 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block1Chunk1Sources 14 0 == 5006
      && tttLargeFiber44ParentOf 5006 == 4942
      && tttLargeFiber44ParentOf 4942 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block1Chunk1Sources 15 0 == 5007
      && tttLargeFiber44ParentOf 5007 == 4943
      && tttLargeFiber44ParentOf 4943 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block1Chunk1Row_0_ok :
    tttLargeFiber44Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_1_ok :
    tttLargeFiber44Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_2_ok :
    tttLargeFiber44Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_3_ok :
    tttLargeFiber44Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_4_ok :
    tttLargeFiber44Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_5_ok :
    tttLargeFiber44Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_6_ok :
    tttLargeFiber44Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_7_ok :
    tttLargeFiber44Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_8_ok :
    tttLargeFiber44Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_9_ok :
    tttLargeFiber44Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_10_ok :
    tttLargeFiber44Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_11_ok :
    tttLargeFiber44Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_12_ok :
    tttLargeFiber44Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_13_ok :
    tttLargeFiber44Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_14_ok :
    tttLargeFiber44Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1Row_15_ok :
    tttLargeFiber44Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_0_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_1_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_2_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_3_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_4_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_5_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_6_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_7_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_8_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_9_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_10_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_11_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_12_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_13_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_14_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentMap_15_ok :
    tttLargeFiber44Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_0_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_1_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_2_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_3_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_4_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_5_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_6_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_7_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_8_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_9_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_10_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_11_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_12_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_13_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_14_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk1ParentPath_15_ok :
    tttLargeFiber44Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber44Block1Chunk1RowCheck 0
    && tttLargeFiber44Block1Chunk1RowCheck 1
    && tttLargeFiber44Block1Chunk1RowCheck 2
    && tttLargeFiber44Block1Chunk1RowCheck 3
    && tttLargeFiber44Block1Chunk1RowCheck 4
    && tttLargeFiber44Block1Chunk1RowCheck 5
    && tttLargeFiber44Block1Chunk1RowCheck 6
    && tttLargeFiber44Block1Chunk1RowCheck 7
    && tttLargeFiber44Block1Chunk1RowCheck 8
    && tttLargeFiber44Block1Chunk1RowCheck 9
    && tttLargeFiber44Block1Chunk1RowCheck 10
    && tttLargeFiber44Block1Chunk1RowCheck 11
    && tttLargeFiber44Block1Chunk1RowCheck 12
    && tttLargeFiber44Block1Chunk1RowCheck 13
    && tttLargeFiber44Block1Chunk1RowCheck 14
    && tttLargeFiber44Block1Chunk1RowCheck 15

theorem tttLargeFiber44Block1Chunk1RowsAudit_ok :
    tttLargeFiber44Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber44Block1Chunk1RowsAudit,
    tttLargeFiber44Block1Chunk1Row_0_ok,
    tttLargeFiber44Block1Chunk1Row_1_ok,
    tttLargeFiber44Block1Chunk1Row_2_ok,
    tttLargeFiber44Block1Chunk1Row_3_ok,
    tttLargeFiber44Block1Chunk1Row_4_ok,
    tttLargeFiber44Block1Chunk1Row_5_ok,
    tttLargeFiber44Block1Chunk1Row_6_ok,
    tttLargeFiber44Block1Chunk1Row_7_ok,
    tttLargeFiber44Block1Chunk1Row_8_ok,
    tttLargeFiber44Block1Chunk1Row_9_ok,
    tttLargeFiber44Block1Chunk1Row_10_ok,
    tttLargeFiber44Block1Chunk1Row_11_ok,
    tttLargeFiber44Block1Chunk1Row_12_ok,
    tttLargeFiber44Block1Chunk1Row_13_ok,
    tttLargeFiber44Block1Chunk1Row_14_ok,
    tttLargeFiber44Block1Chunk1Row_15_ok]

def tttLargeFiber44Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber44Block1Chunk1ParentMapCheck 0
    && tttLargeFiber44Block1Chunk1ParentMapCheck 1
    && tttLargeFiber44Block1Chunk1ParentMapCheck 2
    && tttLargeFiber44Block1Chunk1ParentMapCheck 3
    && tttLargeFiber44Block1Chunk1ParentMapCheck 4
    && tttLargeFiber44Block1Chunk1ParentMapCheck 5
    && tttLargeFiber44Block1Chunk1ParentMapCheck 6
    && tttLargeFiber44Block1Chunk1ParentMapCheck 7
    && tttLargeFiber44Block1Chunk1ParentMapCheck 8
    && tttLargeFiber44Block1Chunk1ParentMapCheck 9
    && tttLargeFiber44Block1Chunk1ParentMapCheck 10
    && tttLargeFiber44Block1Chunk1ParentMapCheck 11
    && tttLargeFiber44Block1Chunk1ParentMapCheck 12
    && tttLargeFiber44Block1Chunk1ParentMapCheck 13
    && tttLargeFiber44Block1Chunk1ParentMapCheck 14
    && tttLargeFiber44Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber44Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber44Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber44Block1Chunk1ParentMapAudit,
    tttLargeFiber44Block1Chunk1ParentMap_0_ok,
    tttLargeFiber44Block1Chunk1ParentMap_1_ok,
    tttLargeFiber44Block1Chunk1ParentMap_2_ok,
    tttLargeFiber44Block1Chunk1ParentMap_3_ok,
    tttLargeFiber44Block1Chunk1ParentMap_4_ok,
    tttLargeFiber44Block1Chunk1ParentMap_5_ok,
    tttLargeFiber44Block1Chunk1ParentMap_6_ok,
    tttLargeFiber44Block1Chunk1ParentMap_7_ok,
    tttLargeFiber44Block1Chunk1ParentMap_8_ok,
    tttLargeFiber44Block1Chunk1ParentMap_9_ok,
    tttLargeFiber44Block1Chunk1ParentMap_10_ok,
    tttLargeFiber44Block1Chunk1ParentMap_11_ok,
    tttLargeFiber44Block1Chunk1ParentMap_12_ok,
    tttLargeFiber44Block1Chunk1ParentMap_13_ok,
    tttLargeFiber44Block1Chunk1ParentMap_14_ok,
    tttLargeFiber44Block1Chunk1ParentMap_15_ok]

def tttLargeFiber44Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber44Block1Chunk1ParentPathCheck 0
    && tttLargeFiber44Block1Chunk1ParentPathCheck 1
    && tttLargeFiber44Block1Chunk1ParentPathCheck 2
    && tttLargeFiber44Block1Chunk1ParentPathCheck 3
    && tttLargeFiber44Block1Chunk1ParentPathCheck 4
    && tttLargeFiber44Block1Chunk1ParentPathCheck 5
    && tttLargeFiber44Block1Chunk1ParentPathCheck 6
    && tttLargeFiber44Block1Chunk1ParentPathCheck 7
    && tttLargeFiber44Block1Chunk1ParentPathCheck 8
    && tttLargeFiber44Block1Chunk1ParentPathCheck 9
    && tttLargeFiber44Block1Chunk1ParentPathCheck 10
    && tttLargeFiber44Block1Chunk1ParentPathCheck 11
    && tttLargeFiber44Block1Chunk1ParentPathCheck 12
    && tttLargeFiber44Block1Chunk1ParentPathCheck 13
    && tttLargeFiber44Block1Chunk1ParentPathCheck 14
    && tttLargeFiber44Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber44Block1Chunk1ParentsAudit_ok :
    tttLargeFiber44Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber44Block1Chunk1ParentsAudit,
    tttLargeFiber44Block1Chunk1ParentPath_0_ok,
    tttLargeFiber44Block1Chunk1ParentPath_1_ok,
    tttLargeFiber44Block1Chunk1ParentPath_2_ok,
    tttLargeFiber44Block1Chunk1ParentPath_3_ok,
    tttLargeFiber44Block1Chunk1ParentPath_4_ok,
    tttLargeFiber44Block1Chunk1ParentPath_5_ok,
    tttLargeFiber44Block1Chunk1ParentPath_6_ok,
    tttLargeFiber44Block1Chunk1ParentPath_7_ok,
    tttLargeFiber44Block1Chunk1ParentPath_8_ok,
    tttLargeFiber44Block1Chunk1ParentPath_9_ok,
    tttLargeFiber44Block1Chunk1ParentPath_10_ok,
    tttLargeFiber44Block1Chunk1ParentPath_11_ok,
    tttLargeFiber44Block1Chunk1ParentPath_12_ok,
    tttLargeFiber44Block1Chunk1ParentPath_13_ok,
    tttLargeFiber44Block1Chunk1ParentPath_14_ok,
    tttLargeFiber44Block1Chunk1ParentPath_15_ok]

def tttLargeFiber44Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block1Chunk1SourcesCheck &&
    tttLargeFiber44Block1Chunk1RowsAudit &&
    tttLargeFiber44Block1Chunk1ParentMapAudit &&
    tttLargeFiber44Block1Chunk1ParentsAudit

theorem tttLargeFiber44Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber44Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block1Chunk1SourcesCheck_ok,
    tttLargeFiber44Block1Chunk1RowsAudit_ok,
    tttLargeFiber44Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber44Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
