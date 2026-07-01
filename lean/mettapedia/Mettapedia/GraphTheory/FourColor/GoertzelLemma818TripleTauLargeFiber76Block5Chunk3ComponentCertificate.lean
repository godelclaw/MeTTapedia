import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 5 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block5Chunk3Sources : List Nat :=
  [   3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671,
   3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679]

def tttLargeFiber76Row368 : TripleComponentParentRow :=
  tripleRow 3664 3792 109 190 64 111 126 64
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row369 : TripleComponentParentRow :=
  tripleRow 3665 3793 109 190 65 111 126 65
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row370 : TripleComponentParentRow :=
  tripleRow 3666 3794 109 190 66 111 126 66
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row371 : TripleComponentParentRow :=
  tripleRow 3667 3651 109 190 67 109 188 135
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

def tttLargeFiber76Row372 : TripleComponentParentRow :=
  tripleRow 3668 3636 109 190 116 109 142 48
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row373 : TripleComponentParentRow :=
  tripleRow 3669 3637 109 190 117 109 142 49
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row374 : TripleComponentParentRow :=
  tripleRow 3670 3798 109 190 118 111 126 118
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row375 : TripleComponentParentRow :=
  tripleRow 3671 3799 109 190 119 111 126 119
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row376 : TripleComponentParentRow :=
  tripleRow 3672 3800 109 191 72 111 127 72
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row377 : TripleComponentParentRow :=
  tripleRow 3673 3801 109 191 73 111 127 73
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row378 : TripleComponentParentRow :=
  tripleRow 3674 3802 109 191 74 111 127 74
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row379 : TripleComponentParentRow :=
  tripleRow 3675 3803 109 191 75 111 127 75
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row380 : TripleComponentParentRow :=
  tripleRow 3676 3644 109 191 124 109 143 56
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row381 : TripleComponentParentRow :=
  tripleRow 3677 3645 109 191 125 109 143 57
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row382 : TripleComponentParentRow :=
  tripleRow 3678 3806 109 191 126 111 127 126
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Row383 : TripleComponentParentRow :=
  tripleRow 3679 3807 109 191 127 111 127 127
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber76Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row368
  , tttLargeFiber76Row369
  , tttLargeFiber76Row370
  , tttLargeFiber76Row371
  , tttLargeFiber76Row372
  , tttLargeFiber76Row373
  , tttLargeFiber76Row374
  , tttLargeFiber76Row375
  , tttLargeFiber76Row376
  , tttLargeFiber76Row377
  , tttLargeFiber76Row378
  , tttLargeFiber76Row379
  , tttLargeFiber76Row380
  , tttLargeFiber76Row381
  , tttLargeFiber76Row382
  , tttLargeFiber76Row383
  ]

def tttLargeFiber76Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber76Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber76Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber76Block5Chunk3Sources

theorem tttLargeFiber76Block5Chunk3SourcesCheck_ok :
    tttLargeFiber76Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber76Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block5Chunk3RowValid
    (listGetD tttLargeFiber76Block5Chunk3Rows i default)

def tttLargeFiber76Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block5Chunk3Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block5Chunk3Sources 0 0 == 3664
      && tttLargeFiber76ParentOf 3664 == 3792
      && tttLargeFiber76ParentOf 3792 == 3040
      && tttLargeFiber76ParentOf 3040 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block5Chunk3Sources 1 0 == 3665
      && tttLargeFiber76ParentOf 3665 == 3793
      && tttLargeFiber76ParentOf 3793 == 3041
      && tttLargeFiber76ParentOf 3041 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block5Chunk3Sources 2 0 == 3666
      && tttLargeFiber76ParentOf 3666 == 3794
      && tttLargeFiber76ParentOf 3794 == 3042
      && tttLargeFiber76ParentOf 3042 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block5Chunk3Sources 3 0 == 3667
      && tttLargeFiber76ParentOf 3667 == 3651
      && tttLargeFiber76ParentOf 3651 == 3619
      && tttLargeFiber76ParentOf 3619 == 3616
      && tttLargeFiber76ParentOf 3616 == 3744
      && tttLargeFiber76ParentOf 3744 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block5Chunk3Sources 4 0 == 3668
      && tttLargeFiber76ParentOf 3668 == 3636
      && tttLargeFiber76ParentOf 3636 == 3624
      && tttLargeFiber76ParentOf 3624 == 3752
      && tttLargeFiber76ParentOf 3752 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block5Chunk3Sources 5 0 == 3669
      && tttLargeFiber76ParentOf 3669 == 3637
      && tttLargeFiber76ParentOf 3637 == 3625
      && tttLargeFiber76ParentOf 3625 == 3753
      && tttLargeFiber76ParentOf 3753 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block5Chunk3Sources 6 0 == 3670
      && tttLargeFiber76ParentOf 3670 == 3798
      && tttLargeFiber76ParentOf 3798 == 3046
      && tttLargeFiber76ParentOf 3046 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block5Chunk3Sources 7 0 == 3671
      && tttLargeFiber76ParentOf 3671 == 3799
      && tttLargeFiber76ParentOf 3799 == 3047
      && tttLargeFiber76ParentOf 3047 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block5Chunk3Sources 8 0 == 3672
      && tttLargeFiber76ParentOf 3672 == 3800
      && tttLargeFiber76ParentOf 3800 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block5Chunk3Sources 9 0 == 3673
      && tttLargeFiber76ParentOf 3673 == 3801
      && tttLargeFiber76ParentOf 3801 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block5Chunk3Sources 10 0 == 3674
      && tttLargeFiber76ParentOf 3674 == 3802
      && tttLargeFiber76ParentOf 3802 == 3050
      && tttLargeFiber76ParentOf 3050 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block5Chunk3Sources 11 0 == 3675
      && tttLargeFiber76ParentOf 3675 == 3803
      && tttLargeFiber76ParentOf 3803 == 3051
      && tttLargeFiber76ParentOf 3051 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block5Chunk3Sources 12 0 == 3676
      && tttLargeFiber76ParentOf 3676 == 3644
      && tttLargeFiber76ParentOf 3644 == 3616
      && tttLargeFiber76ParentOf 3616 == 3744
      && tttLargeFiber76ParentOf 3744 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block5Chunk3Sources 13 0 == 3677
      && tttLargeFiber76ParentOf 3677 == 3645
      && tttLargeFiber76ParentOf 3645 == 3617
      && tttLargeFiber76ParentOf 3617 == 3745
      && tttLargeFiber76ParentOf 3745 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block5Chunk3Sources 14 0 == 3678
      && tttLargeFiber76ParentOf 3678 == 3806
      && tttLargeFiber76ParentOf 3806 == 3054
      && tttLargeFiber76ParentOf 3054 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block5Chunk3Sources 15 0 == 3679
      && tttLargeFiber76ParentOf 3679 == 3807
      && tttLargeFiber76ParentOf 3807 == 3055
      && tttLargeFiber76ParentOf 3055 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block5Chunk3Row_0_ok :
    tttLargeFiber76Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_1_ok :
    tttLargeFiber76Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_2_ok :
    tttLargeFiber76Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_3_ok :
    tttLargeFiber76Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_4_ok :
    tttLargeFiber76Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_5_ok :
    tttLargeFiber76Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_6_ok :
    tttLargeFiber76Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_7_ok :
    tttLargeFiber76Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_8_ok :
    tttLargeFiber76Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_9_ok :
    tttLargeFiber76Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_10_ok :
    tttLargeFiber76Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_11_ok :
    tttLargeFiber76Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_12_ok :
    tttLargeFiber76Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_13_ok :
    tttLargeFiber76Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_14_ok :
    tttLargeFiber76Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3Row_15_ok :
    tttLargeFiber76Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_0_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_1_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_2_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_3_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_4_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_5_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_6_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_7_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_8_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_9_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_10_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_11_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_12_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_13_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_14_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentMap_15_ok :
    tttLargeFiber76Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_0_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_1_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_2_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_3_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_4_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_5_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_6_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_7_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_8_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_9_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_10_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_11_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_12_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_13_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_14_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block5Chunk3ParentPath_15_ok :
    tttLargeFiber76Block5Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber76Block5Chunk3RowCheck 0
    && tttLargeFiber76Block5Chunk3RowCheck 1
    && tttLargeFiber76Block5Chunk3RowCheck 2
    && tttLargeFiber76Block5Chunk3RowCheck 3
    && tttLargeFiber76Block5Chunk3RowCheck 4
    && tttLargeFiber76Block5Chunk3RowCheck 5
    && tttLargeFiber76Block5Chunk3RowCheck 6
    && tttLargeFiber76Block5Chunk3RowCheck 7
    && tttLargeFiber76Block5Chunk3RowCheck 8
    && tttLargeFiber76Block5Chunk3RowCheck 9
    && tttLargeFiber76Block5Chunk3RowCheck 10
    && tttLargeFiber76Block5Chunk3RowCheck 11
    && tttLargeFiber76Block5Chunk3RowCheck 12
    && tttLargeFiber76Block5Chunk3RowCheck 13
    && tttLargeFiber76Block5Chunk3RowCheck 14
    && tttLargeFiber76Block5Chunk3RowCheck 15

theorem tttLargeFiber76Block5Chunk3RowsAudit_ok :
    tttLargeFiber76Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber76Block5Chunk3RowsAudit,
    tttLargeFiber76Block5Chunk3Row_0_ok,
    tttLargeFiber76Block5Chunk3Row_1_ok,
    tttLargeFiber76Block5Chunk3Row_2_ok,
    tttLargeFiber76Block5Chunk3Row_3_ok,
    tttLargeFiber76Block5Chunk3Row_4_ok,
    tttLargeFiber76Block5Chunk3Row_5_ok,
    tttLargeFiber76Block5Chunk3Row_6_ok,
    tttLargeFiber76Block5Chunk3Row_7_ok,
    tttLargeFiber76Block5Chunk3Row_8_ok,
    tttLargeFiber76Block5Chunk3Row_9_ok,
    tttLargeFiber76Block5Chunk3Row_10_ok,
    tttLargeFiber76Block5Chunk3Row_11_ok,
    tttLargeFiber76Block5Chunk3Row_12_ok,
    tttLargeFiber76Block5Chunk3Row_13_ok,
    tttLargeFiber76Block5Chunk3Row_14_ok,
    tttLargeFiber76Block5Chunk3Row_15_ok]

def tttLargeFiber76Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber76Block5Chunk3ParentMapCheck 0
    && tttLargeFiber76Block5Chunk3ParentMapCheck 1
    && tttLargeFiber76Block5Chunk3ParentMapCheck 2
    && tttLargeFiber76Block5Chunk3ParentMapCheck 3
    && tttLargeFiber76Block5Chunk3ParentMapCheck 4
    && tttLargeFiber76Block5Chunk3ParentMapCheck 5
    && tttLargeFiber76Block5Chunk3ParentMapCheck 6
    && tttLargeFiber76Block5Chunk3ParentMapCheck 7
    && tttLargeFiber76Block5Chunk3ParentMapCheck 8
    && tttLargeFiber76Block5Chunk3ParentMapCheck 9
    && tttLargeFiber76Block5Chunk3ParentMapCheck 10
    && tttLargeFiber76Block5Chunk3ParentMapCheck 11
    && tttLargeFiber76Block5Chunk3ParentMapCheck 12
    && tttLargeFiber76Block5Chunk3ParentMapCheck 13
    && tttLargeFiber76Block5Chunk3ParentMapCheck 14
    && tttLargeFiber76Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber76Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber76Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber76Block5Chunk3ParentMapAudit,
    tttLargeFiber76Block5Chunk3ParentMap_0_ok,
    tttLargeFiber76Block5Chunk3ParentMap_1_ok,
    tttLargeFiber76Block5Chunk3ParentMap_2_ok,
    tttLargeFiber76Block5Chunk3ParentMap_3_ok,
    tttLargeFiber76Block5Chunk3ParentMap_4_ok,
    tttLargeFiber76Block5Chunk3ParentMap_5_ok,
    tttLargeFiber76Block5Chunk3ParentMap_6_ok,
    tttLargeFiber76Block5Chunk3ParentMap_7_ok,
    tttLargeFiber76Block5Chunk3ParentMap_8_ok,
    tttLargeFiber76Block5Chunk3ParentMap_9_ok,
    tttLargeFiber76Block5Chunk3ParentMap_10_ok,
    tttLargeFiber76Block5Chunk3ParentMap_11_ok,
    tttLargeFiber76Block5Chunk3ParentMap_12_ok,
    tttLargeFiber76Block5Chunk3ParentMap_13_ok,
    tttLargeFiber76Block5Chunk3ParentMap_14_ok,
    tttLargeFiber76Block5Chunk3ParentMap_15_ok]

def tttLargeFiber76Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber76Block5Chunk3ParentPathCheck 0
    && tttLargeFiber76Block5Chunk3ParentPathCheck 1
    && tttLargeFiber76Block5Chunk3ParentPathCheck 2
    && tttLargeFiber76Block5Chunk3ParentPathCheck 3
    && tttLargeFiber76Block5Chunk3ParentPathCheck 4
    && tttLargeFiber76Block5Chunk3ParentPathCheck 5
    && tttLargeFiber76Block5Chunk3ParentPathCheck 6
    && tttLargeFiber76Block5Chunk3ParentPathCheck 7
    && tttLargeFiber76Block5Chunk3ParentPathCheck 8
    && tttLargeFiber76Block5Chunk3ParentPathCheck 9
    && tttLargeFiber76Block5Chunk3ParentPathCheck 10
    && tttLargeFiber76Block5Chunk3ParentPathCheck 11
    && tttLargeFiber76Block5Chunk3ParentPathCheck 12
    && tttLargeFiber76Block5Chunk3ParentPathCheck 13
    && tttLargeFiber76Block5Chunk3ParentPathCheck 14
    && tttLargeFiber76Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber76Block5Chunk3ParentsAudit_ok :
    tttLargeFiber76Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber76Block5Chunk3ParentsAudit,
    tttLargeFiber76Block5Chunk3ParentPath_0_ok,
    tttLargeFiber76Block5Chunk3ParentPath_1_ok,
    tttLargeFiber76Block5Chunk3ParentPath_2_ok,
    tttLargeFiber76Block5Chunk3ParentPath_3_ok,
    tttLargeFiber76Block5Chunk3ParentPath_4_ok,
    tttLargeFiber76Block5Chunk3ParentPath_5_ok,
    tttLargeFiber76Block5Chunk3ParentPath_6_ok,
    tttLargeFiber76Block5Chunk3ParentPath_7_ok,
    tttLargeFiber76Block5Chunk3ParentPath_8_ok,
    tttLargeFiber76Block5Chunk3ParentPath_9_ok,
    tttLargeFiber76Block5Chunk3ParentPath_10_ok,
    tttLargeFiber76Block5Chunk3ParentPath_11_ok,
    tttLargeFiber76Block5Chunk3ParentPath_12_ok,
    tttLargeFiber76Block5Chunk3ParentPath_13_ok,
    tttLargeFiber76Block5Chunk3ParentPath_14_ok,
    tttLargeFiber76Block5Chunk3ParentPath_15_ok]

def tttLargeFiber76Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block5Chunk3SourcesCheck &&
    tttLargeFiber76Block5Chunk3RowsAudit &&
    tttLargeFiber76Block5Chunk3ParentMapAudit &&
    tttLargeFiber76Block5Chunk3ParentsAudit

theorem tttLargeFiber76Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber76Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block5Chunk3SourcesCheck_ok,
    tttLargeFiber76Block5Chunk3RowsAudit_ok,
    tttLargeFiber76Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber76Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
