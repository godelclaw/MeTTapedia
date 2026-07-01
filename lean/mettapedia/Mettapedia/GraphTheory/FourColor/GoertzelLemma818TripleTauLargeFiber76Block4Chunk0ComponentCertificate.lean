import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 4 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block4Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block4Chunk0Sources : List Nat :=
  [   3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559,
   3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567]

def tttLargeFiber76Row256 : TripleComponentParentRow :=
  tripleRow 3552 3680 108 132 148 110 64 80
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

def tttLargeFiber76Row257 : TripleComponentParentRow :=
  tripleRow 3553 3681 108 132 149 110 64 81
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

def tttLargeFiber76Row258 : TripleComponentParentRow :=
  tripleRow 3554 3682 108 132 150 110 64 82
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
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row259 : TripleComponentParentRow :=
  tripleRow 3555 3552 108 132 151 108 132 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row260 : TripleComponentParentRow :=
  tripleRow 3556 3552 108 132 164 108 132 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row261 : TripleComponentParentRow :=
  tripleRow 3557 3553 108 132 165 108 132 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row262 : TripleComponentParentRow :=
  tripleRow 3558 3686 108 132 166 110 64 102
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

def tttLargeFiber76Row263 : TripleComponentParentRow :=
  tripleRow 3559 3687 108 132 167 110 64 103
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

def tttLargeFiber76Row264 : TripleComponentParentRow :=
  tripleRow 3560 3688 108 133 156 110 65 88
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

def tttLargeFiber76Row265 : TripleComponentParentRow :=
  tripleRow 3561 3689 108 133 157 110 65 89
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

def tttLargeFiber76Row266 : TripleComponentParentRow :=
  tripleRow 3562 3690 108 133 158 110 65 90
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
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row267 : TripleComponentParentRow :=
  tripleRow 3563 3560 108 133 159 108 133 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row268 : TripleComponentParentRow :=
  tripleRow 3564 3560 108 133 172 108 133 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row269 : TripleComponentParentRow :=
  tripleRow 3565 3561 108 133 173 108 133 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row270 : TripleComponentParentRow :=
  tripleRow 3566 3694 108 133 174 110 65 110
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

def tttLargeFiber76Row271 : TripleComponentParentRow :=
  tripleRow 3567 3695 108 133 175 110 65 111
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

def tttLargeFiber76Block4Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row256
  , tttLargeFiber76Row257
  , tttLargeFiber76Row258
  , tttLargeFiber76Row259
  , tttLargeFiber76Row260
  , tttLargeFiber76Row261
  , tttLargeFiber76Row262
  , tttLargeFiber76Row263
  , tttLargeFiber76Row264
  , tttLargeFiber76Row265
  , tttLargeFiber76Row266
  , tttLargeFiber76Row267
  , tttLargeFiber76Row268
  , tttLargeFiber76Row269
  , tttLargeFiber76Row270
  , tttLargeFiber76Row271
  ]

def tttLargeFiber76Block4Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block4Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block4Chunk0ExpectedContains row.source &&
    tttLargeFiber76Block4Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block4Chunk0SourcesCheck : Bool :=
  (tttLargeFiber76Block4Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber76Block4Chunk0Sources

theorem tttLargeFiber76Block4Chunk0SourcesCheck_ok :
    tttLargeFiber76Block4Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber76Block4Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block4Chunk0RowValid
    (listGetD tttLargeFiber76Block4Chunk0Rows i default)

def tttLargeFiber76Block4Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block4Chunk0Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block4Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block4Chunk0Sources 0 0 == 3552
      && tttLargeFiber76ParentOf 3552 == 3680
      && tttLargeFiber76ParentOf 3680 == 3056
      && tttLargeFiber76ParentOf 3056 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block4Chunk0Sources 1 0 == 3553
      && tttLargeFiber76ParentOf 3553 == 3681
      && tttLargeFiber76ParentOf 3681 == 3057
      && tttLargeFiber76ParentOf 3057 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block4Chunk0Sources 2 0 == 3554
      && tttLargeFiber76ParentOf 3554 == 3682
      && tttLargeFiber76ParentOf 3682 == 3058
      && tttLargeFiber76ParentOf 3058 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block4Chunk0Sources 3 0 == 3555
      && tttLargeFiber76ParentOf 3555 == 3552
      && tttLargeFiber76ParentOf 3552 == 3680
      && tttLargeFiber76ParentOf 3680 == 3056
      && tttLargeFiber76ParentOf 3056 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block4Chunk0Sources 4 0 == 3556
      && tttLargeFiber76ParentOf 3556 == 3552
      && tttLargeFiber76ParentOf 3552 == 3680
      && tttLargeFiber76ParentOf 3680 == 3056
      && tttLargeFiber76ParentOf 3056 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block4Chunk0Sources 5 0 == 3557
      && tttLargeFiber76ParentOf 3557 == 3553
      && tttLargeFiber76ParentOf 3553 == 3681
      && tttLargeFiber76ParentOf 3681 == 3057
      && tttLargeFiber76ParentOf 3057 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block4Chunk0Sources 6 0 == 3558
      && tttLargeFiber76ParentOf 3558 == 3686
      && tttLargeFiber76ParentOf 3686 == 3062
      && tttLargeFiber76ParentOf 3062 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block4Chunk0Sources 7 0 == 3559
      && tttLargeFiber76ParentOf 3559 == 3687
      && tttLargeFiber76ParentOf 3687 == 3063
      && tttLargeFiber76ParentOf 3063 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block4Chunk0Sources 8 0 == 3560
      && tttLargeFiber76ParentOf 3560 == 3688
      && tttLargeFiber76ParentOf 3688 == 3064
      && tttLargeFiber76ParentOf 3064 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block4Chunk0Sources 9 0 == 3561
      && tttLargeFiber76ParentOf 3561 == 3689
      && tttLargeFiber76ParentOf 3689 == 3065
      && tttLargeFiber76ParentOf 3065 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block4Chunk0Sources 10 0 == 3562
      && tttLargeFiber76ParentOf 3562 == 3690
      && tttLargeFiber76ParentOf 3690 == 3066
      && tttLargeFiber76ParentOf 3066 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block4Chunk0Sources 11 0 == 3563
      && tttLargeFiber76ParentOf 3563 == 3560
      && tttLargeFiber76ParentOf 3560 == 3688
      && tttLargeFiber76ParentOf 3688 == 3064
      && tttLargeFiber76ParentOf 3064 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block4Chunk0Sources 12 0 == 3564
      && tttLargeFiber76ParentOf 3564 == 3560
      && tttLargeFiber76ParentOf 3560 == 3688
      && tttLargeFiber76ParentOf 3688 == 3064
      && tttLargeFiber76ParentOf 3064 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block4Chunk0Sources 13 0 == 3565
      && tttLargeFiber76ParentOf 3565 == 3561
      && tttLargeFiber76ParentOf 3561 == 3689
      && tttLargeFiber76ParentOf 3689 == 3065
      && tttLargeFiber76ParentOf 3065 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block4Chunk0Sources 14 0 == 3566
      && tttLargeFiber76ParentOf 3566 == 3694
      && tttLargeFiber76ParentOf 3694 == 3070
      && tttLargeFiber76ParentOf 3070 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block4Chunk0Sources 15 0 == 3567
      && tttLargeFiber76ParentOf 3567 == 3695
      && tttLargeFiber76ParentOf 3695 == 3071
      && tttLargeFiber76ParentOf 3071 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block4Chunk0Row_0_ok :
    tttLargeFiber76Block4Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_1_ok :
    tttLargeFiber76Block4Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_2_ok :
    tttLargeFiber76Block4Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_3_ok :
    tttLargeFiber76Block4Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_4_ok :
    tttLargeFiber76Block4Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_5_ok :
    tttLargeFiber76Block4Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_6_ok :
    tttLargeFiber76Block4Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_7_ok :
    tttLargeFiber76Block4Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_8_ok :
    tttLargeFiber76Block4Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_9_ok :
    tttLargeFiber76Block4Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_10_ok :
    tttLargeFiber76Block4Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_11_ok :
    tttLargeFiber76Block4Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_12_ok :
    tttLargeFiber76Block4Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_13_ok :
    tttLargeFiber76Block4Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_14_ok :
    tttLargeFiber76Block4Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0Row_15_ok :
    tttLargeFiber76Block4Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_0_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_1_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_2_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_3_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_4_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_5_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_6_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_7_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_8_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_9_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_10_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_11_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_12_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_13_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_14_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentMap_15_ok :
    tttLargeFiber76Block4Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_0_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_1_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_2_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_3_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_4_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_5_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_6_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_7_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_8_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_9_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_10_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_11_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_12_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_13_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_14_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block4Chunk0ParentPath_15_ok :
    tttLargeFiber76Block4Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block4Chunk0RowsAudit : Bool :=
  tttLargeFiber76Block4Chunk0RowCheck 0
    && tttLargeFiber76Block4Chunk0RowCheck 1
    && tttLargeFiber76Block4Chunk0RowCheck 2
    && tttLargeFiber76Block4Chunk0RowCheck 3
    && tttLargeFiber76Block4Chunk0RowCheck 4
    && tttLargeFiber76Block4Chunk0RowCheck 5
    && tttLargeFiber76Block4Chunk0RowCheck 6
    && tttLargeFiber76Block4Chunk0RowCheck 7
    && tttLargeFiber76Block4Chunk0RowCheck 8
    && tttLargeFiber76Block4Chunk0RowCheck 9
    && tttLargeFiber76Block4Chunk0RowCheck 10
    && tttLargeFiber76Block4Chunk0RowCheck 11
    && tttLargeFiber76Block4Chunk0RowCheck 12
    && tttLargeFiber76Block4Chunk0RowCheck 13
    && tttLargeFiber76Block4Chunk0RowCheck 14
    && tttLargeFiber76Block4Chunk0RowCheck 15

theorem tttLargeFiber76Block4Chunk0RowsAudit_ok :
    tttLargeFiber76Block4Chunk0RowsAudit = true := by
  simp [tttLargeFiber76Block4Chunk0RowsAudit,
    tttLargeFiber76Block4Chunk0Row_0_ok,
    tttLargeFiber76Block4Chunk0Row_1_ok,
    tttLargeFiber76Block4Chunk0Row_2_ok,
    tttLargeFiber76Block4Chunk0Row_3_ok,
    tttLargeFiber76Block4Chunk0Row_4_ok,
    tttLargeFiber76Block4Chunk0Row_5_ok,
    tttLargeFiber76Block4Chunk0Row_6_ok,
    tttLargeFiber76Block4Chunk0Row_7_ok,
    tttLargeFiber76Block4Chunk0Row_8_ok,
    tttLargeFiber76Block4Chunk0Row_9_ok,
    tttLargeFiber76Block4Chunk0Row_10_ok,
    tttLargeFiber76Block4Chunk0Row_11_ok,
    tttLargeFiber76Block4Chunk0Row_12_ok,
    tttLargeFiber76Block4Chunk0Row_13_ok,
    tttLargeFiber76Block4Chunk0Row_14_ok,
    tttLargeFiber76Block4Chunk0Row_15_ok]

def tttLargeFiber76Block4Chunk0ParentMapAudit : Bool :=
  tttLargeFiber76Block4Chunk0ParentMapCheck 0
    && tttLargeFiber76Block4Chunk0ParentMapCheck 1
    && tttLargeFiber76Block4Chunk0ParentMapCheck 2
    && tttLargeFiber76Block4Chunk0ParentMapCheck 3
    && tttLargeFiber76Block4Chunk0ParentMapCheck 4
    && tttLargeFiber76Block4Chunk0ParentMapCheck 5
    && tttLargeFiber76Block4Chunk0ParentMapCheck 6
    && tttLargeFiber76Block4Chunk0ParentMapCheck 7
    && tttLargeFiber76Block4Chunk0ParentMapCheck 8
    && tttLargeFiber76Block4Chunk0ParentMapCheck 9
    && tttLargeFiber76Block4Chunk0ParentMapCheck 10
    && tttLargeFiber76Block4Chunk0ParentMapCheck 11
    && tttLargeFiber76Block4Chunk0ParentMapCheck 12
    && tttLargeFiber76Block4Chunk0ParentMapCheck 13
    && tttLargeFiber76Block4Chunk0ParentMapCheck 14
    && tttLargeFiber76Block4Chunk0ParentMapCheck 15

theorem tttLargeFiber76Block4Chunk0ParentMapAudit_ok :
    tttLargeFiber76Block4Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber76Block4Chunk0ParentMapAudit,
    tttLargeFiber76Block4Chunk0ParentMap_0_ok,
    tttLargeFiber76Block4Chunk0ParentMap_1_ok,
    tttLargeFiber76Block4Chunk0ParentMap_2_ok,
    tttLargeFiber76Block4Chunk0ParentMap_3_ok,
    tttLargeFiber76Block4Chunk0ParentMap_4_ok,
    tttLargeFiber76Block4Chunk0ParentMap_5_ok,
    tttLargeFiber76Block4Chunk0ParentMap_6_ok,
    tttLargeFiber76Block4Chunk0ParentMap_7_ok,
    tttLargeFiber76Block4Chunk0ParentMap_8_ok,
    tttLargeFiber76Block4Chunk0ParentMap_9_ok,
    tttLargeFiber76Block4Chunk0ParentMap_10_ok,
    tttLargeFiber76Block4Chunk0ParentMap_11_ok,
    tttLargeFiber76Block4Chunk0ParentMap_12_ok,
    tttLargeFiber76Block4Chunk0ParentMap_13_ok,
    tttLargeFiber76Block4Chunk0ParentMap_14_ok,
    tttLargeFiber76Block4Chunk0ParentMap_15_ok]

def tttLargeFiber76Block4Chunk0ParentsAudit : Bool :=
  tttLargeFiber76Block4Chunk0ParentPathCheck 0
    && tttLargeFiber76Block4Chunk0ParentPathCheck 1
    && tttLargeFiber76Block4Chunk0ParentPathCheck 2
    && tttLargeFiber76Block4Chunk0ParentPathCheck 3
    && tttLargeFiber76Block4Chunk0ParentPathCheck 4
    && tttLargeFiber76Block4Chunk0ParentPathCheck 5
    && tttLargeFiber76Block4Chunk0ParentPathCheck 6
    && tttLargeFiber76Block4Chunk0ParentPathCheck 7
    && tttLargeFiber76Block4Chunk0ParentPathCheck 8
    && tttLargeFiber76Block4Chunk0ParentPathCheck 9
    && tttLargeFiber76Block4Chunk0ParentPathCheck 10
    && tttLargeFiber76Block4Chunk0ParentPathCheck 11
    && tttLargeFiber76Block4Chunk0ParentPathCheck 12
    && tttLargeFiber76Block4Chunk0ParentPathCheck 13
    && tttLargeFiber76Block4Chunk0ParentPathCheck 14
    && tttLargeFiber76Block4Chunk0ParentPathCheck 15

theorem tttLargeFiber76Block4Chunk0ParentsAudit_ok :
    tttLargeFiber76Block4Chunk0ParentsAudit = true := by
  simp [tttLargeFiber76Block4Chunk0ParentsAudit,
    tttLargeFiber76Block4Chunk0ParentPath_0_ok,
    tttLargeFiber76Block4Chunk0ParentPath_1_ok,
    tttLargeFiber76Block4Chunk0ParentPath_2_ok,
    tttLargeFiber76Block4Chunk0ParentPath_3_ok,
    tttLargeFiber76Block4Chunk0ParentPath_4_ok,
    tttLargeFiber76Block4Chunk0ParentPath_5_ok,
    tttLargeFiber76Block4Chunk0ParentPath_6_ok,
    tttLargeFiber76Block4Chunk0ParentPath_7_ok,
    tttLargeFiber76Block4Chunk0ParentPath_8_ok,
    tttLargeFiber76Block4Chunk0ParentPath_9_ok,
    tttLargeFiber76Block4Chunk0ParentPath_10_ok,
    tttLargeFiber76Block4Chunk0ParentPath_11_ok,
    tttLargeFiber76Block4Chunk0ParentPath_12_ok,
    tttLargeFiber76Block4Chunk0ParentPath_13_ok,
    tttLargeFiber76Block4Chunk0ParentPath_14_ok,
    tttLargeFiber76Block4Chunk0ParentPath_15_ok]

def tttLargeFiber76Block4Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block4Chunk0SourcesCheck &&
    tttLargeFiber76Block4Chunk0RowsAudit &&
    tttLargeFiber76Block4Chunk0ParentMapAudit &&
    tttLargeFiber76Block4Chunk0ParentsAudit

theorem tttLargeFiber76Block4Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber76Block4Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block4Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block4Chunk0SourcesCheck_ok,
    tttLargeFiber76Block4Chunk0RowsAudit_ok,
    tttLargeFiber76Block4Chunk0ParentMapAudit_ok,
    tttLargeFiber76Block4Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block4Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
