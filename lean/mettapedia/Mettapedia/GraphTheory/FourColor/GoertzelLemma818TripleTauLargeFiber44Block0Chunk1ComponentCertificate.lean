import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block0Chunk1Sources : List Nat :=
  [   4928, 4929, 4930, 4931, 4932, 4933, 4934, 4935,
   4936, 4937, 4938, 4939, 4940, 4941, 4942, 4943]

def tttLargeFiber44Row16 : TripleComponentParentRow :=
  tripleRow 4928 4932 148 150 0 148 150 48
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row17 : TripleComponentParentRow :=
  tripleRow 4929 4933 148 150 1 148 150 49
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row18 : TripleComponentParentRow :=
  tripleRow 4930 4924 148 150 2 148 149 172
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row19 : TripleComponentParentRow :=
  tripleRow 4931 4925 148 150 3 148 149 173
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row20 : TripleComponentParentRow :=
  tripleRow 4932 4920 148 150 48 148 149 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row21 : TripleComponentParentRow :=
  tripleRow 4933 4921 148 150 49 148 149 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row22 : TripleComponentParentRow :=
  tripleRow 4934 4922 148 150 50 148 149 158
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row23 : TripleComponentParentRow :=
  tripleRow 4935 4923 148 150 51 148 149 159
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row24 : TripleComponentParentRow :=
  tripleRow 4936 4940 148 151 8 148 151 56
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row25 : TripleComponentParentRow :=
  tripleRow 4937 4941 148 151 9 148 151 57
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row26 : TripleComponentParentRow :=
  tripleRow 4938 4916 148 151 10 148 148 164
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row27 : TripleComponentParentRow :=
  tripleRow 4939 4917 148 151 11 148 148 165
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row28 : TripleComponentParentRow :=
  tripleRow 4940 4912 148 151 56 148 148 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row29 : TripleComponentParentRow :=
  tripleRow 4941 4913 148 151 57 148 148 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row30 : TripleComponentParentRow :=
  tripleRow 4942 4914 148 151 58 148 148 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row31 : TripleComponentParentRow :=
  tripleRow 4943 4915 148 151 59 148 148 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row16
  , tttLargeFiber44Row17
  , tttLargeFiber44Row18
  , tttLargeFiber44Row19
  , tttLargeFiber44Row20
  , tttLargeFiber44Row21
  , tttLargeFiber44Row22
  , tttLargeFiber44Row23
  , tttLargeFiber44Row24
  , tttLargeFiber44Row25
  , tttLargeFiber44Row26
  , tttLargeFiber44Row27
  , tttLargeFiber44Row28
  , tttLargeFiber44Row29
  , tttLargeFiber44Row30
  , tttLargeFiber44Row31
  ]

def tttLargeFiber44Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber44Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber44Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber44Block0Chunk1Sources

theorem tttLargeFiber44Block0Chunk1SourcesCheck_ok :
    tttLargeFiber44Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber44Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block0Chunk1RowValid
    (listGetD tttLargeFiber44Block0Chunk1Rows i default)

def tttLargeFiber44Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block0Chunk1Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block0Chunk1Sources 0 0 == 4928
      && tttLargeFiber44ParentOf 4928 == 4932
      && tttLargeFiber44ParentOf 4932 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block0Chunk1Sources 1 0 == 4929
      && tttLargeFiber44ParentOf 4929 == 4933
      && tttLargeFiber44ParentOf 4933 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block0Chunk1Sources 2 0 == 4930
      && tttLargeFiber44ParentOf 4930 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block0Chunk1Sources 3 0 == 4931
      && tttLargeFiber44ParentOf 4931 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block0Chunk1Sources 4 0 == 4932
      && tttLargeFiber44ParentOf 4932 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block0Chunk1Sources 5 0 == 4933
      && tttLargeFiber44ParentOf 4933 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block0Chunk1Sources 6 0 == 4934
      && tttLargeFiber44ParentOf 4934 == 4922
      && tttLargeFiber44ParentOf 4922 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block0Chunk1Sources 7 0 == 4935
      && tttLargeFiber44ParentOf 4935 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block0Chunk1Sources 8 0 == 4936
      && tttLargeFiber44ParentOf 4936 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block0Chunk1Sources 9 0 == 4937
      && tttLargeFiber44ParentOf 4937 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block0Chunk1Sources 10 0 == 4938
      && tttLargeFiber44ParentOf 4938 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block0Chunk1Sources 11 0 == 4939
      && tttLargeFiber44ParentOf 4939 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block0Chunk1Sources 12 0 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (1 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block0Chunk1Sources 13 0 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block0Chunk1Sources 14 0 == 4942
      && tttLargeFiber44ParentOf 4942 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block0Chunk1Sources 15 0 == 4943
      && tttLargeFiber44ParentOf 4943 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block0Chunk1Row_0_ok :
    tttLargeFiber44Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_1_ok :
    tttLargeFiber44Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_2_ok :
    tttLargeFiber44Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_3_ok :
    tttLargeFiber44Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_4_ok :
    tttLargeFiber44Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_5_ok :
    tttLargeFiber44Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_6_ok :
    tttLargeFiber44Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_7_ok :
    tttLargeFiber44Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_8_ok :
    tttLargeFiber44Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_9_ok :
    tttLargeFiber44Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_10_ok :
    tttLargeFiber44Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_11_ok :
    tttLargeFiber44Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_12_ok :
    tttLargeFiber44Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_13_ok :
    tttLargeFiber44Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_14_ok :
    tttLargeFiber44Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1Row_15_ok :
    tttLargeFiber44Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_0_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_1_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_2_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_3_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_4_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_5_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_6_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_7_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_8_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_9_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_10_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_11_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_12_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_13_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_14_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentMap_15_ok :
    tttLargeFiber44Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_0_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_1_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_2_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_3_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_4_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_5_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_6_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_7_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_8_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_9_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_10_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_11_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_12_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_13_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_14_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block0Chunk1ParentPath_15_ok :
    tttLargeFiber44Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber44Block0Chunk1RowCheck 0
    && tttLargeFiber44Block0Chunk1RowCheck 1
    && tttLargeFiber44Block0Chunk1RowCheck 2
    && tttLargeFiber44Block0Chunk1RowCheck 3
    && tttLargeFiber44Block0Chunk1RowCheck 4
    && tttLargeFiber44Block0Chunk1RowCheck 5
    && tttLargeFiber44Block0Chunk1RowCheck 6
    && tttLargeFiber44Block0Chunk1RowCheck 7
    && tttLargeFiber44Block0Chunk1RowCheck 8
    && tttLargeFiber44Block0Chunk1RowCheck 9
    && tttLargeFiber44Block0Chunk1RowCheck 10
    && tttLargeFiber44Block0Chunk1RowCheck 11
    && tttLargeFiber44Block0Chunk1RowCheck 12
    && tttLargeFiber44Block0Chunk1RowCheck 13
    && tttLargeFiber44Block0Chunk1RowCheck 14
    && tttLargeFiber44Block0Chunk1RowCheck 15

theorem tttLargeFiber44Block0Chunk1RowsAudit_ok :
    tttLargeFiber44Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber44Block0Chunk1RowsAudit,
    tttLargeFiber44Block0Chunk1Row_0_ok,
    tttLargeFiber44Block0Chunk1Row_1_ok,
    tttLargeFiber44Block0Chunk1Row_2_ok,
    tttLargeFiber44Block0Chunk1Row_3_ok,
    tttLargeFiber44Block0Chunk1Row_4_ok,
    tttLargeFiber44Block0Chunk1Row_5_ok,
    tttLargeFiber44Block0Chunk1Row_6_ok,
    tttLargeFiber44Block0Chunk1Row_7_ok,
    tttLargeFiber44Block0Chunk1Row_8_ok,
    tttLargeFiber44Block0Chunk1Row_9_ok,
    tttLargeFiber44Block0Chunk1Row_10_ok,
    tttLargeFiber44Block0Chunk1Row_11_ok,
    tttLargeFiber44Block0Chunk1Row_12_ok,
    tttLargeFiber44Block0Chunk1Row_13_ok,
    tttLargeFiber44Block0Chunk1Row_14_ok,
    tttLargeFiber44Block0Chunk1Row_15_ok]

def tttLargeFiber44Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber44Block0Chunk1ParentMapCheck 0
    && tttLargeFiber44Block0Chunk1ParentMapCheck 1
    && tttLargeFiber44Block0Chunk1ParentMapCheck 2
    && tttLargeFiber44Block0Chunk1ParentMapCheck 3
    && tttLargeFiber44Block0Chunk1ParentMapCheck 4
    && tttLargeFiber44Block0Chunk1ParentMapCheck 5
    && tttLargeFiber44Block0Chunk1ParentMapCheck 6
    && tttLargeFiber44Block0Chunk1ParentMapCheck 7
    && tttLargeFiber44Block0Chunk1ParentMapCheck 8
    && tttLargeFiber44Block0Chunk1ParentMapCheck 9
    && tttLargeFiber44Block0Chunk1ParentMapCheck 10
    && tttLargeFiber44Block0Chunk1ParentMapCheck 11
    && tttLargeFiber44Block0Chunk1ParentMapCheck 12
    && tttLargeFiber44Block0Chunk1ParentMapCheck 13
    && tttLargeFiber44Block0Chunk1ParentMapCheck 14
    && tttLargeFiber44Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber44Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber44Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber44Block0Chunk1ParentMapAudit,
    tttLargeFiber44Block0Chunk1ParentMap_0_ok,
    tttLargeFiber44Block0Chunk1ParentMap_1_ok,
    tttLargeFiber44Block0Chunk1ParentMap_2_ok,
    tttLargeFiber44Block0Chunk1ParentMap_3_ok,
    tttLargeFiber44Block0Chunk1ParentMap_4_ok,
    tttLargeFiber44Block0Chunk1ParentMap_5_ok,
    tttLargeFiber44Block0Chunk1ParentMap_6_ok,
    tttLargeFiber44Block0Chunk1ParentMap_7_ok,
    tttLargeFiber44Block0Chunk1ParentMap_8_ok,
    tttLargeFiber44Block0Chunk1ParentMap_9_ok,
    tttLargeFiber44Block0Chunk1ParentMap_10_ok,
    tttLargeFiber44Block0Chunk1ParentMap_11_ok,
    tttLargeFiber44Block0Chunk1ParentMap_12_ok,
    tttLargeFiber44Block0Chunk1ParentMap_13_ok,
    tttLargeFiber44Block0Chunk1ParentMap_14_ok,
    tttLargeFiber44Block0Chunk1ParentMap_15_ok]

def tttLargeFiber44Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber44Block0Chunk1ParentPathCheck 0
    && tttLargeFiber44Block0Chunk1ParentPathCheck 1
    && tttLargeFiber44Block0Chunk1ParentPathCheck 2
    && tttLargeFiber44Block0Chunk1ParentPathCheck 3
    && tttLargeFiber44Block0Chunk1ParentPathCheck 4
    && tttLargeFiber44Block0Chunk1ParentPathCheck 5
    && tttLargeFiber44Block0Chunk1ParentPathCheck 6
    && tttLargeFiber44Block0Chunk1ParentPathCheck 7
    && tttLargeFiber44Block0Chunk1ParentPathCheck 8
    && tttLargeFiber44Block0Chunk1ParentPathCheck 9
    && tttLargeFiber44Block0Chunk1ParentPathCheck 10
    && tttLargeFiber44Block0Chunk1ParentPathCheck 11
    && tttLargeFiber44Block0Chunk1ParentPathCheck 12
    && tttLargeFiber44Block0Chunk1ParentPathCheck 13
    && tttLargeFiber44Block0Chunk1ParentPathCheck 14
    && tttLargeFiber44Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber44Block0Chunk1ParentsAudit_ok :
    tttLargeFiber44Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber44Block0Chunk1ParentsAudit,
    tttLargeFiber44Block0Chunk1ParentPath_0_ok,
    tttLargeFiber44Block0Chunk1ParentPath_1_ok,
    tttLargeFiber44Block0Chunk1ParentPath_2_ok,
    tttLargeFiber44Block0Chunk1ParentPath_3_ok,
    tttLargeFiber44Block0Chunk1ParentPath_4_ok,
    tttLargeFiber44Block0Chunk1ParentPath_5_ok,
    tttLargeFiber44Block0Chunk1ParentPath_6_ok,
    tttLargeFiber44Block0Chunk1ParentPath_7_ok,
    tttLargeFiber44Block0Chunk1ParentPath_8_ok,
    tttLargeFiber44Block0Chunk1ParentPath_9_ok,
    tttLargeFiber44Block0Chunk1ParentPath_10_ok,
    tttLargeFiber44Block0Chunk1ParentPath_11_ok,
    tttLargeFiber44Block0Chunk1ParentPath_12_ok,
    tttLargeFiber44Block0Chunk1ParentPath_13_ok,
    tttLargeFiber44Block0Chunk1ParentPath_14_ok,
    tttLargeFiber44Block0Chunk1ParentPath_15_ok]

def tttLargeFiber44Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block0Chunk1SourcesCheck &&
    tttLargeFiber44Block0Chunk1RowsAudit &&
    tttLargeFiber44Block0Chunk1ParentMapAudit &&
    tttLargeFiber44Block0Chunk1ParentsAudit

theorem tttLargeFiber44Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber44Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block0Chunk1SourcesCheck_ok,
    tttLargeFiber44Block0Chunk1RowsAudit_ok,
    tttLargeFiber44Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber44Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
