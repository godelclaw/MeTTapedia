import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 4 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block4Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block4Chunk2Sources : List Nat :=
  [   3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591,
   3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599]

def tttLargeFiber76Row288 : TripleComponentParentRow :=
  tripleRow 3584 3600 108 180 132 108 182 64
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row289 : TripleComponentParentRow :=
  tripleRow 3585 3601 108 180 133 108 182 65
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row290 : TripleComponentParentRow :=
  tripleRow 3586 3142 108 180 134 90 18 34
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row291 : TripleComponentParentRow :=
  tripleRow 3587 3143 108 180 135 90 18 35
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row292 : TripleComponentParentRow :=
  tripleRow 3588 3138 108 180 180 90 18 18
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row293 : TripleComponentParentRow :=
  tripleRow 3589 3591 108 180 181 108 180 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row294 : TripleComponentParentRow :=
  tripleRow 3590 3137 108 180 182 90 18 17
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row295 : TripleComponentParentRow :=
  tripleRow 3591 3136 108 180 183 90 18 16
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row296 : TripleComponentParentRow :=
  tripleRow 3592 3608 108 181 140 108 183 72
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row297 : TripleComponentParentRow :=
  tripleRow 3593 3609 108 181 141 108 183 73
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row298 : TripleComponentParentRow :=
  tripleRow 3594 3610 108 181 142 108 183 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
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

def tttLargeFiber76Row299 : TripleComponentParentRow :=
  tripleRow 3595 3592 108 181 143 108 181 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row300 : TripleComponentParentRow :=
  tripleRow 3596 3592 108 181 188 108 181 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row301 : TripleComponentParentRow :=
  tripleRow 3597 3593 108 181 189 108 181 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row302 : TripleComponentParentRow :=
  tripleRow 3598 3614 108 181 190 108 183 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Row303 : TripleComponentParentRow :=
  tripleRow 3599 3615 108 181 191 108 183 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber76Block4Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row288
  , tttLargeFiber76Row289
  , tttLargeFiber76Row290
  , tttLargeFiber76Row291
  , tttLargeFiber76Row292
  , tttLargeFiber76Row293
  , tttLargeFiber76Row294
  , tttLargeFiber76Row295
  , tttLargeFiber76Row296
  , tttLargeFiber76Row297
  , tttLargeFiber76Row298
  , tttLargeFiber76Row299
  , tttLargeFiber76Row300
  , tttLargeFiber76Row301
  , tttLargeFiber76Row302
  , tttLargeFiber76Row303
  ]

def tttLargeFiber76Block4Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block4Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block4Chunk2ExpectedContains row.source &&
    tttLargeFiber76Block4Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block4Chunk2SourcesCheck : Bool :=
  (tttLargeFiber76Block4Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber76Block4Chunk2Sources

theorem tttLargeFiber76Block4Chunk2SourcesCheck_ok :
    tttLargeFiber76Block4Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber76Block4Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block4Chunk2RowValid
    (listGetD tttLargeFiber76Block4Chunk2Rows i default)

def tttLargeFiber76Block4Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block4Chunk2Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block4Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block4Chunk2Sources 0 0 == 3584
      && tttLargeFiber76ParentOf 3584 == 3600
      && tttLargeFiber76ParentOf 3600 == 3128
      && tttLargeFiber76ParentOf 3128 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block4Chunk2Sources 1 0 == 3585
      && tttLargeFiber76ParentOf 3585 == 3601
      && tttLargeFiber76ParentOf 3601 == 3129
      && tttLargeFiber76ParentOf 3129 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block4Chunk2Sources 2 0 == 3586
      && tttLargeFiber76ParentOf 3586 == 3142
      && tttLargeFiber76ParentOf 3142 == 3014
      && tttLargeFiber76ParentOf 3014 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block4Chunk2Sources 3 0 == 3587
      && tttLargeFiber76ParentOf 3587 == 3143
      && tttLargeFiber76ParentOf 3143 == 3015
      && tttLargeFiber76ParentOf 3015 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block4Chunk2Sources 4 0 == 3588
      && tttLargeFiber76ParentOf 3588 == 3138
      && tttLargeFiber76ParentOf 3138 == 3010
      && tttLargeFiber76ParentOf 3010 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block4Chunk2Sources 5 0 == 3589
      && tttLargeFiber76ParentOf 3589 == 3591
      && tttLargeFiber76ParentOf 3591 == 3136
      && tttLargeFiber76ParentOf 3136 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block4Chunk2Sources 6 0 == 3590
      && tttLargeFiber76ParentOf 3590 == 3137
      && tttLargeFiber76ParentOf 3137 == 3009
      && tttLargeFiber76ParentOf 3009 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block4Chunk2Sources 7 0 == 3591
      && tttLargeFiber76ParentOf 3591 == 3136
      && tttLargeFiber76ParentOf 3136 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block4Chunk2Sources 8 0 == 3592
      && tttLargeFiber76ParentOf 3592 == 3608
      && tttLargeFiber76ParentOf 3608 == 3120
      && tttLargeFiber76ParentOf 3120 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block4Chunk2Sources 9 0 == 3593
      && tttLargeFiber76ParentOf 3593 == 3609
      && tttLargeFiber76ParentOf 3609 == 3121
      && tttLargeFiber76ParentOf 3121 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block4Chunk2Sources 10 0 == 3594
      && tttLargeFiber76ParentOf 3594 == 3610
      && tttLargeFiber76ParentOf 3610 == 3122
      && tttLargeFiber76ParentOf 3122 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block4Chunk2Sources 11 0 == 3595
      && tttLargeFiber76ParentOf 3595 == 3592
      && tttLargeFiber76ParentOf 3592 == 3608
      && tttLargeFiber76ParentOf 3608 == 3120
      && tttLargeFiber76ParentOf 3120 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block4Chunk2Sources 12 0 == 3596
      && tttLargeFiber76ParentOf 3596 == 3592
      && tttLargeFiber76ParentOf 3592 == 3608
      && tttLargeFiber76ParentOf 3608 == 3120
      && tttLargeFiber76ParentOf 3120 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block4Chunk2Sources 13 0 == 3597
      && tttLargeFiber76ParentOf 3597 == 3593
      && tttLargeFiber76ParentOf 3593 == 3609
      && tttLargeFiber76ParentOf 3609 == 3121
      && tttLargeFiber76ParentOf 3121 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block4Chunk2Sources 14 0 == 3598
      && tttLargeFiber76ParentOf 3598 == 3614
      && tttLargeFiber76ParentOf 3614 == 3126
      && tttLargeFiber76ParentOf 3126 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block4Chunk2Sources 15 0 == 3599
      && tttLargeFiber76ParentOf 3599 == 3615
      && tttLargeFiber76ParentOf 3615 == 3127
      && tttLargeFiber76ParentOf 3127 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block4Chunk2Row_0_ok :
    tttLargeFiber76Block4Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_1_ok :
    tttLargeFiber76Block4Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_2_ok :
    tttLargeFiber76Block4Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_3_ok :
    tttLargeFiber76Block4Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_4_ok :
    tttLargeFiber76Block4Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_5_ok :
    tttLargeFiber76Block4Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_6_ok :
    tttLargeFiber76Block4Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_7_ok :
    tttLargeFiber76Block4Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_8_ok :
    tttLargeFiber76Block4Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_9_ok :
    tttLargeFiber76Block4Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_10_ok :
    tttLargeFiber76Block4Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_11_ok :
    tttLargeFiber76Block4Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_12_ok :
    tttLargeFiber76Block4Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_13_ok :
    tttLargeFiber76Block4Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_14_ok :
    tttLargeFiber76Block4Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2Row_15_ok :
    tttLargeFiber76Block4Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_0_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_1_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_2_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_3_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_4_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_5_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_6_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_7_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_8_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_9_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_10_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_11_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_12_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_13_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_14_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentMap_15_ok :
    tttLargeFiber76Block4Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_0_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_1_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_2_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_3_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_4_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_5_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_6_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_7_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_8_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_9_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_10_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_11_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_12_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_13_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_14_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block4Chunk2ParentPath_15_ok :
    tttLargeFiber76Block4Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block4Chunk2RowsAudit : Bool :=
  tttLargeFiber76Block4Chunk2RowCheck 0
    && tttLargeFiber76Block4Chunk2RowCheck 1
    && tttLargeFiber76Block4Chunk2RowCheck 2
    && tttLargeFiber76Block4Chunk2RowCheck 3
    && tttLargeFiber76Block4Chunk2RowCheck 4
    && tttLargeFiber76Block4Chunk2RowCheck 5
    && tttLargeFiber76Block4Chunk2RowCheck 6
    && tttLargeFiber76Block4Chunk2RowCheck 7
    && tttLargeFiber76Block4Chunk2RowCheck 8
    && tttLargeFiber76Block4Chunk2RowCheck 9
    && tttLargeFiber76Block4Chunk2RowCheck 10
    && tttLargeFiber76Block4Chunk2RowCheck 11
    && tttLargeFiber76Block4Chunk2RowCheck 12
    && tttLargeFiber76Block4Chunk2RowCheck 13
    && tttLargeFiber76Block4Chunk2RowCheck 14
    && tttLargeFiber76Block4Chunk2RowCheck 15

theorem tttLargeFiber76Block4Chunk2RowsAudit_ok :
    tttLargeFiber76Block4Chunk2RowsAudit = true := by
  simp [tttLargeFiber76Block4Chunk2RowsAudit,
    tttLargeFiber76Block4Chunk2Row_0_ok,
    tttLargeFiber76Block4Chunk2Row_1_ok,
    tttLargeFiber76Block4Chunk2Row_2_ok,
    tttLargeFiber76Block4Chunk2Row_3_ok,
    tttLargeFiber76Block4Chunk2Row_4_ok,
    tttLargeFiber76Block4Chunk2Row_5_ok,
    tttLargeFiber76Block4Chunk2Row_6_ok,
    tttLargeFiber76Block4Chunk2Row_7_ok,
    tttLargeFiber76Block4Chunk2Row_8_ok,
    tttLargeFiber76Block4Chunk2Row_9_ok,
    tttLargeFiber76Block4Chunk2Row_10_ok,
    tttLargeFiber76Block4Chunk2Row_11_ok,
    tttLargeFiber76Block4Chunk2Row_12_ok,
    tttLargeFiber76Block4Chunk2Row_13_ok,
    tttLargeFiber76Block4Chunk2Row_14_ok,
    tttLargeFiber76Block4Chunk2Row_15_ok]

def tttLargeFiber76Block4Chunk2ParentMapAudit : Bool :=
  tttLargeFiber76Block4Chunk2ParentMapCheck 0
    && tttLargeFiber76Block4Chunk2ParentMapCheck 1
    && tttLargeFiber76Block4Chunk2ParentMapCheck 2
    && tttLargeFiber76Block4Chunk2ParentMapCheck 3
    && tttLargeFiber76Block4Chunk2ParentMapCheck 4
    && tttLargeFiber76Block4Chunk2ParentMapCheck 5
    && tttLargeFiber76Block4Chunk2ParentMapCheck 6
    && tttLargeFiber76Block4Chunk2ParentMapCheck 7
    && tttLargeFiber76Block4Chunk2ParentMapCheck 8
    && tttLargeFiber76Block4Chunk2ParentMapCheck 9
    && tttLargeFiber76Block4Chunk2ParentMapCheck 10
    && tttLargeFiber76Block4Chunk2ParentMapCheck 11
    && tttLargeFiber76Block4Chunk2ParentMapCheck 12
    && tttLargeFiber76Block4Chunk2ParentMapCheck 13
    && tttLargeFiber76Block4Chunk2ParentMapCheck 14
    && tttLargeFiber76Block4Chunk2ParentMapCheck 15

theorem tttLargeFiber76Block4Chunk2ParentMapAudit_ok :
    tttLargeFiber76Block4Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber76Block4Chunk2ParentMapAudit,
    tttLargeFiber76Block4Chunk2ParentMap_0_ok,
    tttLargeFiber76Block4Chunk2ParentMap_1_ok,
    tttLargeFiber76Block4Chunk2ParentMap_2_ok,
    tttLargeFiber76Block4Chunk2ParentMap_3_ok,
    tttLargeFiber76Block4Chunk2ParentMap_4_ok,
    tttLargeFiber76Block4Chunk2ParentMap_5_ok,
    tttLargeFiber76Block4Chunk2ParentMap_6_ok,
    tttLargeFiber76Block4Chunk2ParentMap_7_ok,
    tttLargeFiber76Block4Chunk2ParentMap_8_ok,
    tttLargeFiber76Block4Chunk2ParentMap_9_ok,
    tttLargeFiber76Block4Chunk2ParentMap_10_ok,
    tttLargeFiber76Block4Chunk2ParentMap_11_ok,
    tttLargeFiber76Block4Chunk2ParentMap_12_ok,
    tttLargeFiber76Block4Chunk2ParentMap_13_ok,
    tttLargeFiber76Block4Chunk2ParentMap_14_ok,
    tttLargeFiber76Block4Chunk2ParentMap_15_ok]

def tttLargeFiber76Block4Chunk2ParentsAudit : Bool :=
  tttLargeFiber76Block4Chunk2ParentPathCheck 0
    && tttLargeFiber76Block4Chunk2ParentPathCheck 1
    && tttLargeFiber76Block4Chunk2ParentPathCheck 2
    && tttLargeFiber76Block4Chunk2ParentPathCheck 3
    && tttLargeFiber76Block4Chunk2ParentPathCheck 4
    && tttLargeFiber76Block4Chunk2ParentPathCheck 5
    && tttLargeFiber76Block4Chunk2ParentPathCheck 6
    && tttLargeFiber76Block4Chunk2ParentPathCheck 7
    && tttLargeFiber76Block4Chunk2ParentPathCheck 8
    && tttLargeFiber76Block4Chunk2ParentPathCheck 9
    && tttLargeFiber76Block4Chunk2ParentPathCheck 10
    && tttLargeFiber76Block4Chunk2ParentPathCheck 11
    && tttLargeFiber76Block4Chunk2ParentPathCheck 12
    && tttLargeFiber76Block4Chunk2ParentPathCheck 13
    && tttLargeFiber76Block4Chunk2ParentPathCheck 14
    && tttLargeFiber76Block4Chunk2ParentPathCheck 15

theorem tttLargeFiber76Block4Chunk2ParentsAudit_ok :
    tttLargeFiber76Block4Chunk2ParentsAudit = true := by
  simp [tttLargeFiber76Block4Chunk2ParentsAudit,
    tttLargeFiber76Block4Chunk2ParentPath_0_ok,
    tttLargeFiber76Block4Chunk2ParentPath_1_ok,
    tttLargeFiber76Block4Chunk2ParentPath_2_ok,
    tttLargeFiber76Block4Chunk2ParentPath_3_ok,
    tttLargeFiber76Block4Chunk2ParentPath_4_ok,
    tttLargeFiber76Block4Chunk2ParentPath_5_ok,
    tttLargeFiber76Block4Chunk2ParentPath_6_ok,
    tttLargeFiber76Block4Chunk2ParentPath_7_ok,
    tttLargeFiber76Block4Chunk2ParentPath_8_ok,
    tttLargeFiber76Block4Chunk2ParentPath_9_ok,
    tttLargeFiber76Block4Chunk2ParentPath_10_ok,
    tttLargeFiber76Block4Chunk2ParentPath_11_ok,
    tttLargeFiber76Block4Chunk2ParentPath_12_ok,
    tttLargeFiber76Block4Chunk2ParentPath_13_ok,
    tttLargeFiber76Block4Chunk2ParentPath_14_ok,
    tttLargeFiber76Block4Chunk2ParentPath_15_ok]

def tttLargeFiber76Block4Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block4Chunk2SourcesCheck &&
    tttLargeFiber76Block4Chunk2RowsAudit &&
    tttLargeFiber76Block4Chunk2ParentMapAudit &&
    tttLargeFiber76Block4Chunk2ParentsAudit

theorem tttLargeFiber76Block4Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber76Block4Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block4Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block4Chunk2SourcesCheck_ok,
    tttLargeFiber76Block4Chunk2RowsAudit_ok,
    tttLargeFiber76Block4Chunk2ParentMapAudit_ok,
    tttLargeFiber76Block4Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block4Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
