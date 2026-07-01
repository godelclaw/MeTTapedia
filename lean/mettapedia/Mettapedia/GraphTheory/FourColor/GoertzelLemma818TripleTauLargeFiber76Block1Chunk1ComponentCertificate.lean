import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block1Chunk1Sources : List Nat :=
  [   3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079,
   3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]

def tttLargeFiber76Row80 : TripleComponentParentRow :=
  tripleRow 3072 3008 89 90 16 88 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row81 : TripleComponentParentRow :=
  tripleRow 3073 3009 89 90 17 88 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row82 : TripleComponentParentRow :=
  tripleRow 3074 3010 89 90 18 88 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row83 : TripleComponentParentRow :=
  tripleRow 3075 3011 89 90 19 88 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row84 : TripleComponentParentRow :=
  tripleRow 3076 3012 89 90 32 88 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row85 : TripleComponentParentRow :=
  tripleRow 3077 3013 89 90 33 88 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row86 : TripleComponentParentRow :=
  tripleRow 3078 3014 89 90 34 88 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row87 : TripleComponentParentRow :=
  tripleRow 3079 3015 89 90 35 88 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row88 : TripleComponentParentRow :=
  tripleRow 3080 3016 89 91 24 88 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row89 : TripleComponentParentRow :=
  tripleRow 3081 3017 89 91 25 88 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row90 : TripleComponentParentRow :=
  tripleRow 3082 3018 89 91 26 88 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row91 : TripleComponentParentRow :=
  tripleRow 3083 3019 89 91 27 88 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row92 : TripleComponentParentRow :=
  tripleRow 3084 3020 89 91 40 88 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row93 : TripleComponentParentRow :=
  tripleRow 3085 3021 89 91 41 88 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row94 : TripleComponentParentRow :=
  tripleRow 3086 3022 89 91 42 88 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row95 : TripleComponentParentRow :=
  tripleRow 3087 3023 89 91 43 88 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row80
  , tttLargeFiber76Row81
  , tttLargeFiber76Row82
  , tttLargeFiber76Row83
  , tttLargeFiber76Row84
  , tttLargeFiber76Row85
  , tttLargeFiber76Row86
  , tttLargeFiber76Row87
  , tttLargeFiber76Row88
  , tttLargeFiber76Row89
  , tttLargeFiber76Row90
  , tttLargeFiber76Row91
  , tttLargeFiber76Row92
  , tttLargeFiber76Row93
  , tttLargeFiber76Row94
  , tttLargeFiber76Row95
  ]

def tttLargeFiber76Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber76Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber76Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber76Block1Chunk1Sources

theorem tttLargeFiber76Block1Chunk1SourcesCheck_ok :
    tttLargeFiber76Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber76Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block1Chunk1RowValid
    (listGetD tttLargeFiber76Block1Chunk1Rows i default)

def tttLargeFiber76Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block1Chunk1Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block1Chunk1Sources 0 0 == 3072
      && tttLargeFiber76ParentOf 3072 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block1Chunk1Sources 1 0 == 3073
      && tttLargeFiber76ParentOf 3073 == 3009
      && tttLargeFiber76ParentOf 3009 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block1Chunk1Sources 2 0 == 3074
      && tttLargeFiber76ParentOf 3074 == 3010
      && tttLargeFiber76ParentOf 3010 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block1Chunk1Sources 3 0 == 3075
      && tttLargeFiber76ParentOf 3075 == 3011
      && tttLargeFiber76ParentOf 3011 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block1Chunk1Sources 4 0 == 3076
      && tttLargeFiber76ParentOf 3076 == 3012
      && tttLargeFiber76ParentOf 3012 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block1Chunk1Sources 5 0 == 3077
      && tttLargeFiber76ParentOf 3077 == 3013
      && tttLargeFiber76ParentOf 3013 == 3009
      && tttLargeFiber76ParentOf 3009 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block1Chunk1Sources 6 0 == 3078
      && tttLargeFiber76ParentOf 3078 == 3014
      && tttLargeFiber76ParentOf 3014 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block1Chunk1Sources 7 0 == 3079
      && tttLargeFiber76ParentOf 3079 == 3015
      && tttLargeFiber76ParentOf 3015 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block1Chunk1Sources 8 0 == 3080
      && tttLargeFiber76ParentOf 3080 == 3016
      && tttLargeFiber76ParentOf 3016 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block1Chunk1Sources 9 0 == 3081
      && tttLargeFiber76ParentOf 3081 == 3017
      && tttLargeFiber76ParentOf 3017 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block1Chunk1Sources 10 0 == 3082
      && tttLargeFiber76ParentOf 3082 == 3018
      && tttLargeFiber76ParentOf 3018 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block1Chunk1Sources 11 0 == 3083
      && tttLargeFiber76ParentOf 3083 == 3019
      && tttLargeFiber76ParentOf 3019 == 3003
      && tttLargeFiber76ParentOf 3003 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block1Chunk1Sources 12 0 == 3084
      && tttLargeFiber76ParentOf 3084 == 3020
      && tttLargeFiber76ParentOf 3020 == 3016
      && tttLargeFiber76ParentOf 3016 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block1Chunk1Sources 13 0 == 3085
      && tttLargeFiber76ParentOf 3085 == 3021
      && tttLargeFiber76ParentOf 3021 == 3017
      && tttLargeFiber76ParentOf 3017 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block1Chunk1Sources 14 0 == 3086
      && tttLargeFiber76ParentOf 3086 == 3022
      && tttLargeFiber76ParentOf 3022 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block1Chunk1Sources 15 0 == 3087
      && tttLargeFiber76ParentOf 3087 == 3023
      && tttLargeFiber76ParentOf 3023 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block1Chunk1Row_0_ok :
    tttLargeFiber76Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_1_ok :
    tttLargeFiber76Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_2_ok :
    tttLargeFiber76Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_3_ok :
    tttLargeFiber76Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_4_ok :
    tttLargeFiber76Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_5_ok :
    tttLargeFiber76Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_6_ok :
    tttLargeFiber76Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_7_ok :
    tttLargeFiber76Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_8_ok :
    tttLargeFiber76Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_9_ok :
    tttLargeFiber76Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_10_ok :
    tttLargeFiber76Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_11_ok :
    tttLargeFiber76Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_12_ok :
    tttLargeFiber76Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_13_ok :
    tttLargeFiber76Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_14_ok :
    tttLargeFiber76Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1Row_15_ok :
    tttLargeFiber76Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_0_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_1_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_2_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_3_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_4_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_5_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_6_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_7_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_8_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_9_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_10_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_11_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_12_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_13_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_14_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentMap_15_ok :
    tttLargeFiber76Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_0_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_1_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_2_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_3_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_4_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_5_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_6_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_7_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_8_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_9_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_10_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_11_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_12_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_13_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_14_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk1ParentPath_15_ok :
    tttLargeFiber76Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber76Block1Chunk1RowCheck 0
    && tttLargeFiber76Block1Chunk1RowCheck 1
    && tttLargeFiber76Block1Chunk1RowCheck 2
    && tttLargeFiber76Block1Chunk1RowCheck 3
    && tttLargeFiber76Block1Chunk1RowCheck 4
    && tttLargeFiber76Block1Chunk1RowCheck 5
    && tttLargeFiber76Block1Chunk1RowCheck 6
    && tttLargeFiber76Block1Chunk1RowCheck 7
    && tttLargeFiber76Block1Chunk1RowCheck 8
    && tttLargeFiber76Block1Chunk1RowCheck 9
    && tttLargeFiber76Block1Chunk1RowCheck 10
    && tttLargeFiber76Block1Chunk1RowCheck 11
    && tttLargeFiber76Block1Chunk1RowCheck 12
    && tttLargeFiber76Block1Chunk1RowCheck 13
    && tttLargeFiber76Block1Chunk1RowCheck 14
    && tttLargeFiber76Block1Chunk1RowCheck 15

theorem tttLargeFiber76Block1Chunk1RowsAudit_ok :
    tttLargeFiber76Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber76Block1Chunk1RowsAudit,
    tttLargeFiber76Block1Chunk1Row_0_ok,
    tttLargeFiber76Block1Chunk1Row_1_ok,
    tttLargeFiber76Block1Chunk1Row_2_ok,
    tttLargeFiber76Block1Chunk1Row_3_ok,
    tttLargeFiber76Block1Chunk1Row_4_ok,
    tttLargeFiber76Block1Chunk1Row_5_ok,
    tttLargeFiber76Block1Chunk1Row_6_ok,
    tttLargeFiber76Block1Chunk1Row_7_ok,
    tttLargeFiber76Block1Chunk1Row_8_ok,
    tttLargeFiber76Block1Chunk1Row_9_ok,
    tttLargeFiber76Block1Chunk1Row_10_ok,
    tttLargeFiber76Block1Chunk1Row_11_ok,
    tttLargeFiber76Block1Chunk1Row_12_ok,
    tttLargeFiber76Block1Chunk1Row_13_ok,
    tttLargeFiber76Block1Chunk1Row_14_ok,
    tttLargeFiber76Block1Chunk1Row_15_ok]

def tttLargeFiber76Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber76Block1Chunk1ParentMapCheck 0
    && tttLargeFiber76Block1Chunk1ParentMapCheck 1
    && tttLargeFiber76Block1Chunk1ParentMapCheck 2
    && tttLargeFiber76Block1Chunk1ParentMapCheck 3
    && tttLargeFiber76Block1Chunk1ParentMapCheck 4
    && tttLargeFiber76Block1Chunk1ParentMapCheck 5
    && tttLargeFiber76Block1Chunk1ParentMapCheck 6
    && tttLargeFiber76Block1Chunk1ParentMapCheck 7
    && tttLargeFiber76Block1Chunk1ParentMapCheck 8
    && tttLargeFiber76Block1Chunk1ParentMapCheck 9
    && tttLargeFiber76Block1Chunk1ParentMapCheck 10
    && tttLargeFiber76Block1Chunk1ParentMapCheck 11
    && tttLargeFiber76Block1Chunk1ParentMapCheck 12
    && tttLargeFiber76Block1Chunk1ParentMapCheck 13
    && tttLargeFiber76Block1Chunk1ParentMapCheck 14
    && tttLargeFiber76Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber76Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber76Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber76Block1Chunk1ParentMapAudit,
    tttLargeFiber76Block1Chunk1ParentMap_0_ok,
    tttLargeFiber76Block1Chunk1ParentMap_1_ok,
    tttLargeFiber76Block1Chunk1ParentMap_2_ok,
    tttLargeFiber76Block1Chunk1ParentMap_3_ok,
    tttLargeFiber76Block1Chunk1ParentMap_4_ok,
    tttLargeFiber76Block1Chunk1ParentMap_5_ok,
    tttLargeFiber76Block1Chunk1ParentMap_6_ok,
    tttLargeFiber76Block1Chunk1ParentMap_7_ok,
    tttLargeFiber76Block1Chunk1ParentMap_8_ok,
    tttLargeFiber76Block1Chunk1ParentMap_9_ok,
    tttLargeFiber76Block1Chunk1ParentMap_10_ok,
    tttLargeFiber76Block1Chunk1ParentMap_11_ok,
    tttLargeFiber76Block1Chunk1ParentMap_12_ok,
    tttLargeFiber76Block1Chunk1ParentMap_13_ok,
    tttLargeFiber76Block1Chunk1ParentMap_14_ok,
    tttLargeFiber76Block1Chunk1ParentMap_15_ok]

def tttLargeFiber76Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber76Block1Chunk1ParentPathCheck 0
    && tttLargeFiber76Block1Chunk1ParentPathCheck 1
    && tttLargeFiber76Block1Chunk1ParentPathCheck 2
    && tttLargeFiber76Block1Chunk1ParentPathCheck 3
    && tttLargeFiber76Block1Chunk1ParentPathCheck 4
    && tttLargeFiber76Block1Chunk1ParentPathCheck 5
    && tttLargeFiber76Block1Chunk1ParentPathCheck 6
    && tttLargeFiber76Block1Chunk1ParentPathCheck 7
    && tttLargeFiber76Block1Chunk1ParentPathCheck 8
    && tttLargeFiber76Block1Chunk1ParentPathCheck 9
    && tttLargeFiber76Block1Chunk1ParentPathCheck 10
    && tttLargeFiber76Block1Chunk1ParentPathCheck 11
    && tttLargeFiber76Block1Chunk1ParentPathCheck 12
    && tttLargeFiber76Block1Chunk1ParentPathCheck 13
    && tttLargeFiber76Block1Chunk1ParentPathCheck 14
    && tttLargeFiber76Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber76Block1Chunk1ParentsAudit_ok :
    tttLargeFiber76Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber76Block1Chunk1ParentsAudit,
    tttLargeFiber76Block1Chunk1ParentPath_0_ok,
    tttLargeFiber76Block1Chunk1ParentPath_1_ok,
    tttLargeFiber76Block1Chunk1ParentPath_2_ok,
    tttLargeFiber76Block1Chunk1ParentPath_3_ok,
    tttLargeFiber76Block1Chunk1ParentPath_4_ok,
    tttLargeFiber76Block1Chunk1ParentPath_5_ok,
    tttLargeFiber76Block1Chunk1ParentPath_6_ok,
    tttLargeFiber76Block1Chunk1ParentPath_7_ok,
    tttLargeFiber76Block1Chunk1ParentPath_8_ok,
    tttLargeFiber76Block1Chunk1ParentPath_9_ok,
    tttLargeFiber76Block1Chunk1ParentPath_10_ok,
    tttLargeFiber76Block1Chunk1ParentPath_11_ok,
    tttLargeFiber76Block1Chunk1ParentPath_12_ok,
    tttLargeFiber76Block1Chunk1ParentPath_13_ok,
    tttLargeFiber76Block1Chunk1ParentPath_14_ok,
    tttLargeFiber76Block1Chunk1ParentPath_15_ok]

def tttLargeFiber76Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block1Chunk1SourcesCheck &&
    tttLargeFiber76Block1Chunk1RowsAudit &&
    tttLargeFiber76Block1Chunk1ParentMapAudit &&
    tttLargeFiber76Block1Chunk1ParentsAudit

theorem tttLargeFiber76Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber76Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block1Chunk1SourcesCheck_ok,
    tttLargeFiber76Block1Chunk1RowsAudit_ok,
    tttLargeFiber76Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber76Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
