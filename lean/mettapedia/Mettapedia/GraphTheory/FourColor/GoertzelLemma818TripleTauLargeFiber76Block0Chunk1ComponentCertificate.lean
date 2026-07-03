import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 0 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block0Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block0Chunk1Sources : List Nat :=
  [   3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015,
   3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]

def tttLargeFiber76Row16 : TripleComponentParentRow :=
  tripleRow 3008 2992 88 82 16 88 80 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row17 : TripleComponentParentRow :=
  tripleRow 3009 2993 88 82 17 88 80 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row18 : TripleComponentParentRow :=
  tripleRow 3010 2994 88 82 18 88 80 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row19 : TripleComponentParentRow :=
  tripleRow 3011 2995 88 82 19 88 80 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row20 : TripleComponentParentRow :=
  tripleRow 3012 3008 88 82 32 88 82 16
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row21 : TripleComponentParentRow :=
  tripleRow 3013 3009 88 82 33 88 82 17
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row22 : TripleComponentParentRow :=
  tripleRow 3014 2998 88 82 34 88 80 102
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

def tttLargeFiber76Row23 : TripleComponentParentRow :=
  tripleRow 3015 2999 88 82 35 88 80 103
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

def tttLargeFiber76Row24 : TripleComponentParentRow :=
  tripleRow 3016 3000 88 83 24 88 81 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row25 : TripleComponentParentRow :=
  tripleRow 3017 3001 88 83 25 88 81 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row26 : TripleComponentParentRow :=
  tripleRow 3018 3002 88 83 26 88 81 90
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row27 : TripleComponentParentRow :=
  tripleRow 3019 3003 88 83 27 88 81 91
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row28 : TripleComponentParentRow :=
  tripleRow 3020 3016 88 83 40 88 83 24
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row29 : TripleComponentParentRow :=
  tripleRow 3021 3017 88 83 41 88 83 25
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row30 : TripleComponentParentRow :=
  tripleRow 3022 3006 88 83 42 88 81 110
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row31 : TripleComponentParentRow :=
  tripleRow 3023 3007 88 83 43 88 81 111
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Block0Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row16
  , tttLargeFiber76Row17
  , tttLargeFiber76Row18
  , tttLargeFiber76Row19
  , tttLargeFiber76Row20
  , tttLargeFiber76Row21
  , tttLargeFiber76Row22
  , tttLargeFiber76Row23
  , tttLargeFiber76Row24
  , tttLargeFiber76Row25
  , tttLargeFiber76Row26
  , tttLargeFiber76Row27
  , tttLargeFiber76Row28
  , tttLargeFiber76Row29
  , tttLargeFiber76Row30
  , tttLargeFiber76Row31
  ]

def tttLargeFiber76Block0Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block0Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block0Chunk1ExpectedContains row.source &&
    tttLargeFiber76Block0Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block0Chunk1SourcesCheck : Bool :=
  (tttLargeFiber76Block0Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber76Block0Chunk1Sources

theorem tttLargeFiber76Block0Chunk1SourcesCheck_ok :
    tttLargeFiber76Block0Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber76Block0Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block0Chunk1RowValid
    (listGetD tttLargeFiber76Block0Chunk1Rows i default)

def tttLargeFiber76Block0Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block0Chunk1Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block0Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block0Chunk1Sources 0 0 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (1 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block0Chunk1Sources 1 0 == 3009
      && tttLargeFiber76ParentOf 3009 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block0Chunk1Sources 2 0 == 3010
      && tttLargeFiber76ParentOf 3010 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block0Chunk1Sources 3 0 == 3011
      && tttLargeFiber76ParentOf 3011 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block0Chunk1Sources 4 0 == 3012
      && tttLargeFiber76ParentOf 3012 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block0Chunk1Sources 5 0 == 3013
      && tttLargeFiber76ParentOf 3013 == 3009
      && tttLargeFiber76ParentOf 3009 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block0Chunk1Sources 6 0 == 3014
      && tttLargeFiber76ParentOf 3014 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block0Chunk1Sources 7 0 == 3015
      && tttLargeFiber76ParentOf 3015 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block0Chunk1Sources 8 0 == 3016
      && tttLargeFiber76ParentOf 3016 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block0Chunk1Sources 9 0 == 3017
      && tttLargeFiber76ParentOf 3017 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block0Chunk1Sources 10 0 == 3018
      && tttLargeFiber76ParentOf 3018 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block0Chunk1Sources 11 0 == 3019
      && tttLargeFiber76ParentOf 3019 == 3003
      && tttLargeFiber76ParentOf 3003 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block0Chunk1Sources 12 0 == 3020
      && tttLargeFiber76ParentOf 3020 == 3016
      && tttLargeFiber76ParentOf 3016 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block0Chunk1Sources 13 0 == 3021
      && tttLargeFiber76ParentOf 3021 == 3017
      && tttLargeFiber76ParentOf 3017 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block0Chunk1Sources 14 0 == 3022
      && tttLargeFiber76ParentOf 3022 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block0Chunk1Sources 15 0 == 3023
      && tttLargeFiber76ParentOf 3023 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block0Chunk1Row_0_ok :
    tttLargeFiber76Block0Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_1_ok :
    tttLargeFiber76Block0Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_2_ok :
    tttLargeFiber76Block0Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_3_ok :
    tttLargeFiber76Block0Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_4_ok :
    tttLargeFiber76Block0Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_5_ok :
    tttLargeFiber76Block0Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_6_ok :
    tttLargeFiber76Block0Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_7_ok :
    tttLargeFiber76Block0Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_8_ok :
    tttLargeFiber76Block0Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_9_ok :
    tttLargeFiber76Block0Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_10_ok :
    tttLargeFiber76Block0Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_11_ok :
    tttLargeFiber76Block0Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_12_ok :
    tttLargeFiber76Block0Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_13_ok :
    tttLargeFiber76Block0Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_14_ok :
    tttLargeFiber76Block0Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1Row_15_ok :
    tttLargeFiber76Block0Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_0_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_1_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_2_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_3_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_4_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_5_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_6_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_7_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_8_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_9_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_10_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_11_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_12_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_13_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_14_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentMap_15_ok :
    tttLargeFiber76Block0Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_0_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_1_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_2_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_3_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_4_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_5_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_6_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_7_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_8_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_9_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_10_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_11_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_12_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_13_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_14_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block0Chunk1ParentPath_15_ok :
    tttLargeFiber76Block0Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block0Chunk1RowsAudit : Bool :=
  tttLargeFiber76Block0Chunk1RowCheck 0
    && tttLargeFiber76Block0Chunk1RowCheck 1
    && tttLargeFiber76Block0Chunk1RowCheck 2
    && tttLargeFiber76Block0Chunk1RowCheck 3
    && tttLargeFiber76Block0Chunk1RowCheck 4
    && tttLargeFiber76Block0Chunk1RowCheck 5
    && tttLargeFiber76Block0Chunk1RowCheck 6
    && tttLargeFiber76Block0Chunk1RowCheck 7
    && tttLargeFiber76Block0Chunk1RowCheck 8
    && tttLargeFiber76Block0Chunk1RowCheck 9
    && tttLargeFiber76Block0Chunk1RowCheck 10
    && tttLargeFiber76Block0Chunk1RowCheck 11
    && tttLargeFiber76Block0Chunk1RowCheck 12
    && tttLargeFiber76Block0Chunk1RowCheck 13
    && tttLargeFiber76Block0Chunk1RowCheck 14
    && tttLargeFiber76Block0Chunk1RowCheck 15

theorem tttLargeFiber76Block0Chunk1RowsAudit_ok :
    tttLargeFiber76Block0Chunk1RowsAudit = true := by
  simp [tttLargeFiber76Block0Chunk1RowsAudit,
    tttLargeFiber76Block0Chunk1Row_0_ok,
    tttLargeFiber76Block0Chunk1Row_1_ok,
    tttLargeFiber76Block0Chunk1Row_2_ok,
    tttLargeFiber76Block0Chunk1Row_3_ok,
    tttLargeFiber76Block0Chunk1Row_4_ok,
    tttLargeFiber76Block0Chunk1Row_5_ok,
    tttLargeFiber76Block0Chunk1Row_6_ok,
    tttLargeFiber76Block0Chunk1Row_7_ok,
    tttLargeFiber76Block0Chunk1Row_8_ok,
    tttLargeFiber76Block0Chunk1Row_9_ok,
    tttLargeFiber76Block0Chunk1Row_10_ok,
    tttLargeFiber76Block0Chunk1Row_11_ok,
    tttLargeFiber76Block0Chunk1Row_12_ok,
    tttLargeFiber76Block0Chunk1Row_13_ok,
    tttLargeFiber76Block0Chunk1Row_14_ok,
    tttLargeFiber76Block0Chunk1Row_15_ok]

def tttLargeFiber76Block0Chunk1ParentMapAudit : Bool :=
  tttLargeFiber76Block0Chunk1ParentMapCheck 0
    && tttLargeFiber76Block0Chunk1ParentMapCheck 1
    && tttLargeFiber76Block0Chunk1ParentMapCheck 2
    && tttLargeFiber76Block0Chunk1ParentMapCheck 3
    && tttLargeFiber76Block0Chunk1ParentMapCheck 4
    && tttLargeFiber76Block0Chunk1ParentMapCheck 5
    && tttLargeFiber76Block0Chunk1ParentMapCheck 6
    && tttLargeFiber76Block0Chunk1ParentMapCheck 7
    && tttLargeFiber76Block0Chunk1ParentMapCheck 8
    && tttLargeFiber76Block0Chunk1ParentMapCheck 9
    && tttLargeFiber76Block0Chunk1ParentMapCheck 10
    && tttLargeFiber76Block0Chunk1ParentMapCheck 11
    && tttLargeFiber76Block0Chunk1ParentMapCheck 12
    && tttLargeFiber76Block0Chunk1ParentMapCheck 13
    && tttLargeFiber76Block0Chunk1ParentMapCheck 14
    && tttLargeFiber76Block0Chunk1ParentMapCheck 15

theorem tttLargeFiber76Block0Chunk1ParentMapAudit_ok :
    tttLargeFiber76Block0Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber76Block0Chunk1ParentMapAudit,
    tttLargeFiber76Block0Chunk1ParentMap_0_ok,
    tttLargeFiber76Block0Chunk1ParentMap_1_ok,
    tttLargeFiber76Block0Chunk1ParentMap_2_ok,
    tttLargeFiber76Block0Chunk1ParentMap_3_ok,
    tttLargeFiber76Block0Chunk1ParentMap_4_ok,
    tttLargeFiber76Block0Chunk1ParentMap_5_ok,
    tttLargeFiber76Block0Chunk1ParentMap_6_ok,
    tttLargeFiber76Block0Chunk1ParentMap_7_ok,
    tttLargeFiber76Block0Chunk1ParentMap_8_ok,
    tttLargeFiber76Block0Chunk1ParentMap_9_ok,
    tttLargeFiber76Block0Chunk1ParentMap_10_ok,
    tttLargeFiber76Block0Chunk1ParentMap_11_ok,
    tttLargeFiber76Block0Chunk1ParentMap_12_ok,
    tttLargeFiber76Block0Chunk1ParentMap_13_ok,
    tttLargeFiber76Block0Chunk1ParentMap_14_ok,
    tttLargeFiber76Block0Chunk1ParentMap_15_ok]

def tttLargeFiber76Block0Chunk1ParentsAudit : Bool :=
  tttLargeFiber76Block0Chunk1ParentPathCheck 0
    && tttLargeFiber76Block0Chunk1ParentPathCheck 1
    && tttLargeFiber76Block0Chunk1ParentPathCheck 2
    && tttLargeFiber76Block0Chunk1ParentPathCheck 3
    && tttLargeFiber76Block0Chunk1ParentPathCheck 4
    && tttLargeFiber76Block0Chunk1ParentPathCheck 5
    && tttLargeFiber76Block0Chunk1ParentPathCheck 6
    && tttLargeFiber76Block0Chunk1ParentPathCheck 7
    && tttLargeFiber76Block0Chunk1ParentPathCheck 8
    && tttLargeFiber76Block0Chunk1ParentPathCheck 9
    && tttLargeFiber76Block0Chunk1ParentPathCheck 10
    && tttLargeFiber76Block0Chunk1ParentPathCheck 11
    && tttLargeFiber76Block0Chunk1ParentPathCheck 12
    && tttLargeFiber76Block0Chunk1ParentPathCheck 13
    && tttLargeFiber76Block0Chunk1ParentPathCheck 14
    && tttLargeFiber76Block0Chunk1ParentPathCheck 15

theorem tttLargeFiber76Block0Chunk1ParentsAudit_ok :
    tttLargeFiber76Block0Chunk1ParentsAudit = true := by
  simp [tttLargeFiber76Block0Chunk1ParentsAudit,
    tttLargeFiber76Block0Chunk1ParentPath_0_ok,
    tttLargeFiber76Block0Chunk1ParentPath_1_ok,
    tttLargeFiber76Block0Chunk1ParentPath_2_ok,
    tttLargeFiber76Block0Chunk1ParentPath_3_ok,
    tttLargeFiber76Block0Chunk1ParentPath_4_ok,
    tttLargeFiber76Block0Chunk1ParentPath_5_ok,
    tttLargeFiber76Block0Chunk1ParentPath_6_ok,
    tttLargeFiber76Block0Chunk1ParentPath_7_ok,
    tttLargeFiber76Block0Chunk1ParentPath_8_ok,
    tttLargeFiber76Block0Chunk1ParentPath_9_ok,
    tttLargeFiber76Block0Chunk1ParentPath_10_ok,
    tttLargeFiber76Block0Chunk1ParentPath_11_ok,
    tttLargeFiber76Block0Chunk1ParentPath_12_ok,
    tttLargeFiber76Block0Chunk1ParentPath_13_ok,
    tttLargeFiber76Block0Chunk1ParentPath_14_ok,
    tttLargeFiber76Block0Chunk1ParentPath_15_ok]

def tttLargeFiber76Block0Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block0Chunk1SourcesCheck &&
    tttLargeFiber76Block0Chunk1RowsAudit &&
    tttLargeFiber76Block0Chunk1ParentMapAudit &&
    tttLargeFiber76Block0Chunk1ParentsAudit

theorem tttLargeFiber76Block0Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber76Block0Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block0Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block0Chunk1SourcesCheck_ok,
    tttLargeFiber76Block0Chunk1RowsAudit_ok,
    tttLargeFiber76Block0Chunk1ParentMapAudit_ok,
    tttLargeFiber76Block0Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block0Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
