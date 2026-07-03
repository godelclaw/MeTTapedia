import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 7 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block7Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block7Chunk0Sources : List Nat :=
  [   5648, 5649, 5650, 5651, 5652, 5653, 5654, 5655,
   5656, 5657, 5658, 5659, 5660, 5661, 5662, 5663]

def tttLargeFiber44Row448 : TripleComponentParentRow :=
  tripleRow 5648 5520 167 72 80 165 140 148
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row449 : TripleComponentParentRow :=
  tripleRow 5649 5521 167 72 81 165 140 149
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row450 : TripleComponentParentRow :=
  tripleRow 5650 5648 167 72 82 167 72 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row451 : TripleComponentParentRow :=
  tripleRow 5651 5523 167 72 83 165 140 151
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row452 : TripleComponentParentRow :=
  tripleRow 5652 5524 167 72 100 165 140 164
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row453 : TripleComponentParentRow :=
  tripleRow 5653 5525 167 72 101 165 140 165
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row454 : TripleComponentParentRow :=
  tripleRow 5654 5649 167 72 102 167 72 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row455 : TripleComponentParentRow :=
  tripleRow 5655 5648 167 72 103 167 72 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Row456 : TripleComponentParentRow :=
  tripleRow 5656 5528 167 73 88 165 141 156
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row457 : TripleComponentParentRow :=
  tripleRow 5657 5529 167 73 89 165 141 157
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row458 : TripleComponentParentRow :=
  tripleRow 5658 5656 167 73 90 167 73 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row459 : TripleComponentParentRow :=
  tripleRow 5659 5531 167 73 91 165 141 159
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row460 : TripleComponentParentRow :=
  tripleRow 5660 5532 167 73 108 165 141 172
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row461 : TripleComponentParentRow :=
  tripleRow 5661 5533 167 73 109 165 141 173
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row462 : TripleComponentParentRow :=
  tripleRow 5662 5657 167 73 110 167 73 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row463 : TripleComponentParentRow :=
  tripleRow 5663 5656 167 73 111 167 73 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Block7Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row448
  , tttLargeFiber44Row449
  , tttLargeFiber44Row450
  , tttLargeFiber44Row451
  , tttLargeFiber44Row452
  , tttLargeFiber44Row453
  , tttLargeFiber44Row454
  , tttLargeFiber44Row455
  , tttLargeFiber44Row456
  , tttLargeFiber44Row457
  , tttLargeFiber44Row458
  , tttLargeFiber44Row459
  , tttLargeFiber44Row460
  , tttLargeFiber44Row461
  , tttLargeFiber44Row462
  , tttLargeFiber44Row463
  ]

def tttLargeFiber44Block7Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block7Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block7Chunk0ExpectedContains row.source &&
    tttLargeFiber44Block7Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block7Chunk0SourcesCheck : Bool :=
  (tttLargeFiber44Block7Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber44Block7Chunk0Sources

theorem tttLargeFiber44Block7Chunk0SourcesCheck_ok :
    tttLargeFiber44Block7Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber44Block7Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block7Chunk0RowValid
    (listGetD tttLargeFiber44Block7Chunk0Rows i default)

def tttLargeFiber44Block7Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block7Chunk0Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block7Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block7Chunk0Sources 0 0 == 5648
      && tttLargeFiber44ParentOf 5648 == 5520
      && tttLargeFiber44ParentOf 5520 == 4976
      && tttLargeFiber44ParentOf 4976 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block7Chunk0Sources 1 0 == 5649
      && tttLargeFiber44ParentOf 5649 == 5521
      && tttLargeFiber44ParentOf 5521 == 4977
      && tttLargeFiber44ParentOf 4977 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block7Chunk0Sources 2 0 == 5650
      && tttLargeFiber44ParentOf 5650 == 5648
      && tttLargeFiber44ParentOf 5648 == 5520
      && tttLargeFiber44ParentOf 5520 == 4976
      && tttLargeFiber44ParentOf 4976 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block7Chunk0Sources 3 0 == 5651
      && tttLargeFiber44ParentOf 5651 == 5523
      && tttLargeFiber44ParentOf 5523 == 4979
      && tttLargeFiber44ParentOf 4979 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block7Chunk0Sources 4 0 == 5652
      && tttLargeFiber44ParentOf 5652 == 5524
      && tttLargeFiber44ParentOf 5524 == 4980
      && tttLargeFiber44ParentOf 4980 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block7Chunk0Sources 5 0 == 5653
      && tttLargeFiber44ParentOf 5653 == 5525
      && tttLargeFiber44ParentOf 5525 == 4981
      && tttLargeFiber44ParentOf 4981 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block7Chunk0Sources 6 0 == 5654
      && tttLargeFiber44ParentOf 5654 == 5649
      && tttLargeFiber44ParentOf 5649 == 5521
      && tttLargeFiber44ParentOf 5521 == 4977
      && tttLargeFiber44ParentOf 4977 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block7Chunk0Sources 7 0 == 5655
      && tttLargeFiber44ParentOf 5655 == 5648
      && tttLargeFiber44ParentOf 5648 == 5520
      && tttLargeFiber44ParentOf 5520 == 4976
      && tttLargeFiber44ParentOf 4976 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block7Chunk0Sources 8 0 == 5656
      && tttLargeFiber44ParentOf 5656 == 5528
      && tttLargeFiber44ParentOf 5528 == 4984
      && tttLargeFiber44ParentOf 4984 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block7Chunk0Sources 9 0 == 5657
      && tttLargeFiber44ParentOf 5657 == 5529
      && tttLargeFiber44ParentOf 5529 == 4985
      && tttLargeFiber44ParentOf 4985 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block7Chunk0Sources 10 0 == 5658
      && tttLargeFiber44ParentOf 5658 == 5656
      && tttLargeFiber44ParentOf 5656 == 5528
      && tttLargeFiber44ParentOf 5528 == 4984
      && tttLargeFiber44ParentOf 4984 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block7Chunk0Sources 11 0 == 5659
      && tttLargeFiber44ParentOf 5659 == 5531
      && tttLargeFiber44ParentOf 5531 == 4987
      && tttLargeFiber44ParentOf 4987 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block7Chunk0Sources 12 0 == 5660
      && tttLargeFiber44ParentOf 5660 == 5532
      && tttLargeFiber44ParentOf 5532 == 4988
      && tttLargeFiber44ParentOf 4988 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block7Chunk0Sources 13 0 == 5661
      && tttLargeFiber44ParentOf 5661 == 5533
      && tttLargeFiber44ParentOf 5533 == 4989
      && tttLargeFiber44ParentOf 4989 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (6 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block7Chunk0Sources 14 0 == 5662
      && tttLargeFiber44ParentOf 5662 == 5657
      && tttLargeFiber44ParentOf 5657 == 5529
      && tttLargeFiber44ParentOf 5529 == 4985
      && tttLargeFiber44ParentOf 4985 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (6 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block7Chunk0Sources 15 0 == 5663
      && tttLargeFiber44ParentOf 5663 == 5656
      && tttLargeFiber44ParentOf 5656 == 5528
      && tttLargeFiber44ParentOf 5528 == 4984
      && tttLargeFiber44ParentOf 4984 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block7Chunk0Row_0_ok :
    tttLargeFiber44Block7Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_1_ok :
    tttLargeFiber44Block7Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_2_ok :
    tttLargeFiber44Block7Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_3_ok :
    tttLargeFiber44Block7Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_4_ok :
    tttLargeFiber44Block7Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_5_ok :
    tttLargeFiber44Block7Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_6_ok :
    tttLargeFiber44Block7Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_7_ok :
    tttLargeFiber44Block7Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_8_ok :
    tttLargeFiber44Block7Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_9_ok :
    tttLargeFiber44Block7Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_10_ok :
    tttLargeFiber44Block7Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_11_ok :
    tttLargeFiber44Block7Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_12_ok :
    tttLargeFiber44Block7Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_13_ok :
    tttLargeFiber44Block7Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_14_ok :
    tttLargeFiber44Block7Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0Row_15_ok :
    tttLargeFiber44Block7Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_0_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_1_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_2_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_3_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_4_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_5_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_6_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_7_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_8_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_9_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_10_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_11_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_12_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_13_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_14_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentMap_15_ok :
    tttLargeFiber44Block7Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_0_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_1_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_2_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_3_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_4_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_5_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_6_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_7_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_8_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_9_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_10_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_11_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_12_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_13_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_14_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block7Chunk0ParentPath_15_ok :
    tttLargeFiber44Block7Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block7Chunk0RowsAudit : Bool :=
  tttLargeFiber44Block7Chunk0RowCheck 0
    && tttLargeFiber44Block7Chunk0RowCheck 1
    && tttLargeFiber44Block7Chunk0RowCheck 2
    && tttLargeFiber44Block7Chunk0RowCheck 3
    && tttLargeFiber44Block7Chunk0RowCheck 4
    && tttLargeFiber44Block7Chunk0RowCheck 5
    && tttLargeFiber44Block7Chunk0RowCheck 6
    && tttLargeFiber44Block7Chunk0RowCheck 7
    && tttLargeFiber44Block7Chunk0RowCheck 8
    && tttLargeFiber44Block7Chunk0RowCheck 9
    && tttLargeFiber44Block7Chunk0RowCheck 10
    && tttLargeFiber44Block7Chunk0RowCheck 11
    && tttLargeFiber44Block7Chunk0RowCheck 12
    && tttLargeFiber44Block7Chunk0RowCheck 13
    && tttLargeFiber44Block7Chunk0RowCheck 14
    && tttLargeFiber44Block7Chunk0RowCheck 15

theorem tttLargeFiber44Block7Chunk0RowsAudit_ok :
    tttLargeFiber44Block7Chunk0RowsAudit = true := by
  simp [tttLargeFiber44Block7Chunk0RowsAudit,
    tttLargeFiber44Block7Chunk0Row_0_ok,
    tttLargeFiber44Block7Chunk0Row_1_ok,
    tttLargeFiber44Block7Chunk0Row_2_ok,
    tttLargeFiber44Block7Chunk0Row_3_ok,
    tttLargeFiber44Block7Chunk0Row_4_ok,
    tttLargeFiber44Block7Chunk0Row_5_ok,
    tttLargeFiber44Block7Chunk0Row_6_ok,
    tttLargeFiber44Block7Chunk0Row_7_ok,
    tttLargeFiber44Block7Chunk0Row_8_ok,
    tttLargeFiber44Block7Chunk0Row_9_ok,
    tttLargeFiber44Block7Chunk0Row_10_ok,
    tttLargeFiber44Block7Chunk0Row_11_ok,
    tttLargeFiber44Block7Chunk0Row_12_ok,
    tttLargeFiber44Block7Chunk0Row_13_ok,
    tttLargeFiber44Block7Chunk0Row_14_ok,
    tttLargeFiber44Block7Chunk0Row_15_ok]

def tttLargeFiber44Block7Chunk0ParentMapAudit : Bool :=
  tttLargeFiber44Block7Chunk0ParentMapCheck 0
    && tttLargeFiber44Block7Chunk0ParentMapCheck 1
    && tttLargeFiber44Block7Chunk0ParentMapCheck 2
    && tttLargeFiber44Block7Chunk0ParentMapCheck 3
    && tttLargeFiber44Block7Chunk0ParentMapCheck 4
    && tttLargeFiber44Block7Chunk0ParentMapCheck 5
    && tttLargeFiber44Block7Chunk0ParentMapCheck 6
    && tttLargeFiber44Block7Chunk0ParentMapCheck 7
    && tttLargeFiber44Block7Chunk0ParentMapCheck 8
    && tttLargeFiber44Block7Chunk0ParentMapCheck 9
    && tttLargeFiber44Block7Chunk0ParentMapCheck 10
    && tttLargeFiber44Block7Chunk0ParentMapCheck 11
    && tttLargeFiber44Block7Chunk0ParentMapCheck 12
    && tttLargeFiber44Block7Chunk0ParentMapCheck 13
    && tttLargeFiber44Block7Chunk0ParentMapCheck 14
    && tttLargeFiber44Block7Chunk0ParentMapCheck 15

theorem tttLargeFiber44Block7Chunk0ParentMapAudit_ok :
    tttLargeFiber44Block7Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber44Block7Chunk0ParentMapAudit,
    tttLargeFiber44Block7Chunk0ParentMap_0_ok,
    tttLargeFiber44Block7Chunk0ParentMap_1_ok,
    tttLargeFiber44Block7Chunk0ParentMap_2_ok,
    tttLargeFiber44Block7Chunk0ParentMap_3_ok,
    tttLargeFiber44Block7Chunk0ParentMap_4_ok,
    tttLargeFiber44Block7Chunk0ParentMap_5_ok,
    tttLargeFiber44Block7Chunk0ParentMap_6_ok,
    tttLargeFiber44Block7Chunk0ParentMap_7_ok,
    tttLargeFiber44Block7Chunk0ParentMap_8_ok,
    tttLargeFiber44Block7Chunk0ParentMap_9_ok,
    tttLargeFiber44Block7Chunk0ParentMap_10_ok,
    tttLargeFiber44Block7Chunk0ParentMap_11_ok,
    tttLargeFiber44Block7Chunk0ParentMap_12_ok,
    tttLargeFiber44Block7Chunk0ParentMap_13_ok,
    tttLargeFiber44Block7Chunk0ParentMap_14_ok,
    tttLargeFiber44Block7Chunk0ParentMap_15_ok]

def tttLargeFiber44Block7Chunk0ParentsAudit : Bool :=
  tttLargeFiber44Block7Chunk0ParentPathCheck 0
    && tttLargeFiber44Block7Chunk0ParentPathCheck 1
    && tttLargeFiber44Block7Chunk0ParentPathCheck 2
    && tttLargeFiber44Block7Chunk0ParentPathCheck 3
    && tttLargeFiber44Block7Chunk0ParentPathCheck 4
    && tttLargeFiber44Block7Chunk0ParentPathCheck 5
    && tttLargeFiber44Block7Chunk0ParentPathCheck 6
    && tttLargeFiber44Block7Chunk0ParentPathCheck 7
    && tttLargeFiber44Block7Chunk0ParentPathCheck 8
    && tttLargeFiber44Block7Chunk0ParentPathCheck 9
    && tttLargeFiber44Block7Chunk0ParentPathCheck 10
    && tttLargeFiber44Block7Chunk0ParentPathCheck 11
    && tttLargeFiber44Block7Chunk0ParentPathCheck 12
    && tttLargeFiber44Block7Chunk0ParentPathCheck 13
    && tttLargeFiber44Block7Chunk0ParentPathCheck 14
    && tttLargeFiber44Block7Chunk0ParentPathCheck 15

theorem tttLargeFiber44Block7Chunk0ParentsAudit_ok :
    tttLargeFiber44Block7Chunk0ParentsAudit = true := by
  simp [tttLargeFiber44Block7Chunk0ParentsAudit,
    tttLargeFiber44Block7Chunk0ParentPath_0_ok,
    tttLargeFiber44Block7Chunk0ParentPath_1_ok,
    tttLargeFiber44Block7Chunk0ParentPath_2_ok,
    tttLargeFiber44Block7Chunk0ParentPath_3_ok,
    tttLargeFiber44Block7Chunk0ParentPath_4_ok,
    tttLargeFiber44Block7Chunk0ParentPath_5_ok,
    tttLargeFiber44Block7Chunk0ParentPath_6_ok,
    tttLargeFiber44Block7Chunk0ParentPath_7_ok,
    tttLargeFiber44Block7Chunk0ParentPath_8_ok,
    tttLargeFiber44Block7Chunk0ParentPath_9_ok,
    tttLargeFiber44Block7Chunk0ParentPath_10_ok,
    tttLargeFiber44Block7Chunk0ParentPath_11_ok,
    tttLargeFiber44Block7Chunk0ParentPath_12_ok,
    tttLargeFiber44Block7Chunk0ParentPath_13_ok,
    tttLargeFiber44Block7Chunk0ParentPath_14_ok,
    tttLargeFiber44Block7Chunk0ParentPath_15_ok]

def tttLargeFiber44Block7Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block7Chunk0SourcesCheck &&
    tttLargeFiber44Block7Chunk0RowsAudit &&
    tttLargeFiber44Block7Chunk0ParentMapAudit &&
    tttLargeFiber44Block7Chunk0ParentsAudit

theorem tttLargeFiber44Block7Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber44Block7Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block7Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block7Chunk0SourcesCheck_ok,
    tttLargeFiber44Block7Chunk0RowsAudit_ok,
    tttLargeFiber44Block7Chunk0ParentMapAudit_ok,
    tttLargeFiber44Block7Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block7Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
