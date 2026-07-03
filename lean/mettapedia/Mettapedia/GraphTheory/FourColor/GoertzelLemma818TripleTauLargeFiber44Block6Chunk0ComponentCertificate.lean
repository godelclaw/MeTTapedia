import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 6 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block6Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block6Chunk0Sources : List Nat :=
  [   5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591,
   5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599]

def tttLargeFiber44Row384 : TripleComponentParentRow :=
  tripleRow 5584 5456 166 64 80 164 132 148
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

def tttLargeFiber44Row385 : TripleComponentParentRow :=
  tripleRow 5585 5457 166 64 81 164 132 149
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

def tttLargeFiber44Row386 : TripleComponentParentRow :=
  tripleRow 5586 5584 166 64 82 166 64 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row387 : TripleComponentParentRow :=
  tripleRow 5587 5459 166 64 83 164 132 151
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row388 : TripleComponentParentRow :=
  tripleRow 5588 5460 166 64 100 164 132 164
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

def tttLargeFiber44Row389 : TripleComponentParentRow :=
  tripleRow 5589 5461 166 64 101 164 132 165
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

def tttLargeFiber44Row390 : TripleComponentParentRow :=
  tripleRow 5590 5585 166 64 102 166 64 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row391 : TripleComponentParentRow :=
  tripleRow 5591 5584 166 64 103 166 64 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Row392 : TripleComponentParentRow :=
  tripleRow 5592 5464 166 65 88 164 133 156
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

def tttLargeFiber44Row393 : TripleComponentParentRow :=
  tripleRow 5593 5465 166 65 89 164 133 157
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

def tttLargeFiber44Row394 : TripleComponentParentRow :=
  tripleRow 5594 5592 166 65 90 166 65 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row395 : TripleComponentParentRow :=
  tripleRow 5595 5467 166 65 91 164 133 159
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
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row396 : TripleComponentParentRow :=
  tripleRow 5596 5468 166 65 108 164 133 172
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

def tttLargeFiber44Row397 : TripleComponentParentRow :=
  tripleRow 5597 5469 166 65 109 164 133 173
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

def tttLargeFiber44Row398 : TripleComponentParentRow :=
  tripleRow 5598 5593 166 65 110 166 65 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row399 : TripleComponentParentRow :=
  tripleRow 5599 5592 166 65 111 166 65 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Block6Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row384
  , tttLargeFiber44Row385
  , tttLargeFiber44Row386
  , tttLargeFiber44Row387
  , tttLargeFiber44Row388
  , tttLargeFiber44Row389
  , tttLargeFiber44Row390
  , tttLargeFiber44Row391
  , tttLargeFiber44Row392
  , tttLargeFiber44Row393
  , tttLargeFiber44Row394
  , tttLargeFiber44Row395
  , tttLargeFiber44Row396
  , tttLargeFiber44Row397
  , tttLargeFiber44Row398
  , tttLargeFiber44Row399
  ]

def tttLargeFiber44Block6Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block6Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block6Chunk0ExpectedContains row.source &&
    tttLargeFiber44Block6Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block6Chunk0SourcesCheck : Bool :=
  (tttLargeFiber44Block6Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber44Block6Chunk0Sources

theorem tttLargeFiber44Block6Chunk0SourcesCheck_ok :
    tttLargeFiber44Block6Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber44Block6Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block6Chunk0RowValid
    (listGetD tttLargeFiber44Block6Chunk0Rows i default)

def tttLargeFiber44Block6Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block6Chunk0Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block6Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block6Chunk0Sources 0 0 == 5584
      && tttLargeFiber44ParentOf 5584 == 5456
      && tttLargeFiber44ParentOf 5456 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block6Chunk0Sources 1 0 == 5585
      && tttLargeFiber44ParentOf 5585 == 5457
      && tttLargeFiber44ParentOf 5457 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block6Chunk0Sources 2 0 == 5586
      && tttLargeFiber44ParentOf 5586 == 5584
      && tttLargeFiber44ParentOf 5584 == 5456
      && tttLargeFiber44ParentOf 5456 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block6Chunk0Sources 3 0 == 5587
      && tttLargeFiber44ParentOf 5587 == 5459
      && tttLargeFiber44ParentOf 5459 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block6Chunk0Sources 4 0 == 5588
      && tttLargeFiber44ParentOf 5588 == 5460
      && tttLargeFiber44ParentOf 5460 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block6Chunk0Sources 5 0 == 5589
      && tttLargeFiber44ParentOf 5589 == 5461
      && tttLargeFiber44ParentOf 5461 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block6Chunk0Sources 6 0 == 5590
      && tttLargeFiber44ParentOf 5590 == 5585
      && tttLargeFiber44ParentOf 5585 == 5457
      && tttLargeFiber44ParentOf 5457 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block6Chunk0Sources 7 0 == 5591
      && tttLargeFiber44ParentOf 5591 == 5584
      && tttLargeFiber44ParentOf 5584 == 5456
      && tttLargeFiber44ParentOf 5456 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block6Chunk0Sources 8 0 == 5592
      && tttLargeFiber44ParentOf 5592 == 5464
      && tttLargeFiber44ParentOf 5464 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block6Chunk0Sources 9 0 == 5593
      && tttLargeFiber44ParentOf 5593 == 5465
      && tttLargeFiber44ParentOf 5465 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block6Chunk0Sources 10 0 == 5594
      && tttLargeFiber44ParentOf 5594 == 5592
      && tttLargeFiber44ParentOf 5592 == 5464
      && tttLargeFiber44ParentOf 5464 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block6Chunk0Sources 11 0 == 5595
      && tttLargeFiber44ParentOf 5595 == 5467
      && tttLargeFiber44ParentOf 5467 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block6Chunk0Sources 12 0 == 5596
      && tttLargeFiber44ParentOf 5596 == 5468
      && tttLargeFiber44ParentOf 5468 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block6Chunk0Sources 13 0 == 5597
      && tttLargeFiber44ParentOf 5597 == 5469
      && tttLargeFiber44ParentOf 5469 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block6Chunk0Sources 14 0 == 5598
      && tttLargeFiber44ParentOf 5598 == 5593
      && tttLargeFiber44ParentOf 5593 == 5465
      && tttLargeFiber44ParentOf 5465 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block6Chunk0Sources 15 0 == 5599
      && tttLargeFiber44ParentOf 5599 == 5592
      && tttLargeFiber44ParentOf 5592 == 5464
      && tttLargeFiber44ParentOf 5464 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block6Chunk0Row_0_ok :
    tttLargeFiber44Block6Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_1_ok :
    tttLargeFiber44Block6Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_2_ok :
    tttLargeFiber44Block6Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_3_ok :
    tttLargeFiber44Block6Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_4_ok :
    tttLargeFiber44Block6Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_5_ok :
    tttLargeFiber44Block6Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_6_ok :
    tttLargeFiber44Block6Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_7_ok :
    tttLargeFiber44Block6Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_8_ok :
    tttLargeFiber44Block6Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_9_ok :
    tttLargeFiber44Block6Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_10_ok :
    tttLargeFiber44Block6Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_11_ok :
    tttLargeFiber44Block6Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_12_ok :
    tttLargeFiber44Block6Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_13_ok :
    tttLargeFiber44Block6Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_14_ok :
    tttLargeFiber44Block6Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0Row_15_ok :
    tttLargeFiber44Block6Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_0_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_1_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_2_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_3_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_4_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_5_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_6_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_7_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_8_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_9_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_10_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_11_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_12_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_13_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_14_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentMap_15_ok :
    tttLargeFiber44Block6Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_0_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_1_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_2_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_3_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_4_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_5_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_6_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_7_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_8_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_9_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_10_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_11_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_12_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_13_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_14_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block6Chunk0ParentPath_15_ok :
    tttLargeFiber44Block6Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block6Chunk0RowsAudit : Bool :=
  tttLargeFiber44Block6Chunk0RowCheck 0
    && tttLargeFiber44Block6Chunk0RowCheck 1
    && tttLargeFiber44Block6Chunk0RowCheck 2
    && tttLargeFiber44Block6Chunk0RowCheck 3
    && tttLargeFiber44Block6Chunk0RowCheck 4
    && tttLargeFiber44Block6Chunk0RowCheck 5
    && tttLargeFiber44Block6Chunk0RowCheck 6
    && tttLargeFiber44Block6Chunk0RowCheck 7
    && tttLargeFiber44Block6Chunk0RowCheck 8
    && tttLargeFiber44Block6Chunk0RowCheck 9
    && tttLargeFiber44Block6Chunk0RowCheck 10
    && tttLargeFiber44Block6Chunk0RowCheck 11
    && tttLargeFiber44Block6Chunk0RowCheck 12
    && tttLargeFiber44Block6Chunk0RowCheck 13
    && tttLargeFiber44Block6Chunk0RowCheck 14
    && tttLargeFiber44Block6Chunk0RowCheck 15

theorem tttLargeFiber44Block6Chunk0RowsAudit_ok :
    tttLargeFiber44Block6Chunk0RowsAudit = true := by
  simp [tttLargeFiber44Block6Chunk0RowsAudit,
    tttLargeFiber44Block6Chunk0Row_0_ok,
    tttLargeFiber44Block6Chunk0Row_1_ok,
    tttLargeFiber44Block6Chunk0Row_2_ok,
    tttLargeFiber44Block6Chunk0Row_3_ok,
    tttLargeFiber44Block6Chunk0Row_4_ok,
    tttLargeFiber44Block6Chunk0Row_5_ok,
    tttLargeFiber44Block6Chunk0Row_6_ok,
    tttLargeFiber44Block6Chunk0Row_7_ok,
    tttLargeFiber44Block6Chunk0Row_8_ok,
    tttLargeFiber44Block6Chunk0Row_9_ok,
    tttLargeFiber44Block6Chunk0Row_10_ok,
    tttLargeFiber44Block6Chunk0Row_11_ok,
    tttLargeFiber44Block6Chunk0Row_12_ok,
    tttLargeFiber44Block6Chunk0Row_13_ok,
    tttLargeFiber44Block6Chunk0Row_14_ok,
    tttLargeFiber44Block6Chunk0Row_15_ok]

def tttLargeFiber44Block6Chunk0ParentMapAudit : Bool :=
  tttLargeFiber44Block6Chunk0ParentMapCheck 0
    && tttLargeFiber44Block6Chunk0ParentMapCheck 1
    && tttLargeFiber44Block6Chunk0ParentMapCheck 2
    && tttLargeFiber44Block6Chunk0ParentMapCheck 3
    && tttLargeFiber44Block6Chunk0ParentMapCheck 4
    && tttLargeFiber44Block6Chunk0ParentMapCheck 5
    && tttLargeFiber44Block6Chunk0ParentMapCheck 6
    && tttLargeFiber44Block6Chunk0ParentMapCheck 7
    && tttLargeFiber44Block6Chunk0ParentMapCheck 8
    && tttLargeFiber44Block6Chunk0ParentMapCheck 9
    && tttLargeFiber44Block6Chunk0ParentMapCheck 10
    && tttLargeFiber44Block6Chunk0ParentMapCheck 11
    && tttLargeFiber44Block6Chunk0ParentMapCheck 12
    && tttLargeFiber44Block6Chunk0ParentMapCheck 13
    && tttLargeFiber44Block6Chunk0ParentMapCheck 14
    && tttLargeFiber44Block6Chunk0ParentMapCheck 15

theorem tttLargeFiber44Block6Chunk0ParentMapAudit_ok :
    tttLargeFiber44Block6Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber44Block6Chunk0ParentMapAudit,
    tttLargeFiber44Block6Chunk0ParentMap_0_ok,
    tttLargeFiber44Block6Chunk0ParentMap_1_ok,
    tttLargeFiber44Block6Chunk0ParentMap_2_ok,
    tttLargeFiber44Block6Chunk0ParentMap_3_ok,
    tttLargeFiber44Block6Chunk0ParentMap_4_ok,
    tttLargeFiber44Block6Chunk0ParentMap_5_ok,
    tttLargeFiber44Block6Chunk0ParentMap_6_ok,
    tttLargeFiber44Block6Chunk0ParentMap_7_ok,
    tttLargeFiber44Block6Chunk0ParentMap_8_ok,
    tttLargeFiber44Block6Chunk0ParentMap_9_ok,
    tttLargeFiber44Block6Chunk0ParentMap_10_ok,
    tttLargeFiber44Block6Chunk0ParentMap_11_ok,
    tttLargeFiber44Block6Chunk0ParentMap_12_ok,
    tttLargeFiber44Block6Chunk0ParentMap_13_ok,
    tttLargeFiber44Block6Chunk0ParentMap_14_ok,
    tttLargeFiber44Block6Chunk0ParentMap_15_ok]

def tttLargeFiber44Block6Chunk0ParentsAudit : Bool :=
  tttLargeFiber44Block6Chunk0ParentPathCheck 0
    && tttLargeFiber44Block6Chunk0ParentPathCheck 1
    && tttLargeFiber44Block6Chunk0ParentPathCheck 2
    && tttLargeFiber44Block6Chunk0ParentPathCheck 3
    && tttLargeFiber44Block6Chunk0ParentPathCheck 4
    && tttLargeFiber44Block6Chunk0ParentPathCheck 5
    && tttLargeFiber44Block6Chunk0ParentPathCheck 6
    && tttLargeFiber44Block6Chunk0ParentPathCheck 7
    && tttLargeFiber44Block6Chunk0ParentPathCheck 8
    && tttLargeFiber44Block6Chunk0ParentPathCheck 9
    && tttLargeFiber44Block6Chunk0ParentPathCheck 10
    && tttLargeFiber44Block6Chunk0ParentPathCheck 11
    && tttLargeFiber44Block6Chunk0ParentPathCheck 12
    && tttLargeFiber44Block6Chunk0ParentPathCheck 13
    && tttLargeFiber44Block6Chunk0ParentPathCheck 14
    && tttLargeFiber44Block6Chunk0ParentPathCheck 15

theorem tttLargeFiber44Block6Chunk0ParentsAudit_ok :
    tttLargeFiber44Block6Chunk0ParentsAudit = true := by
  simp [tttLargeFiber44Block6Chunk0ParentsAudit,
    tttLargeFiber44Block6Chunk0ParentPath_0_ok,
    tttLargeFiber44Block6Chunk0ParentPath_1_ok,
    tttLargeFiber44Block6Chunk0ParentPath_2_ok,
    tttLargeFiber44Block6Chunk0ParentPath_3_ok,
    tttLargeFiber44Block6Chunk0ParentPath_4_ok,
    tttLargeFiber44Block6Chunk0ParentPath_5_ok,
    tttLargeFiber44Block6Chunk0ParentPath_6_ok,
    tttLargeFiber44Block6Chunk0ParentPath_7_ok,
    tttLargeFiber44Block6Chunk0ParentPath_8_ok,
    tttLargeFiber44Block6Chunk0ParentPath_9_ok,
    tttLargeFiber44Block6Chunk0ParentPath_10_ok,
    tttLargeFiber44Block6Chunk0ParentPath_11_ok,
    tttLargeFiber44Block6Chunk0ParentPath_12_ok,
    tttLargeFiber44Block6Chunk0ParentPath_13_ok,
    tttLargeFiber44Block6Chunk0ParentPath_14_ok,
    tttLargeFiber44Block6Chunk0ParentPath_15_ok]

def tttLargeFiber44Block6Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block6Chunk0SourcesCheck &&
    tttLargeFiber44Block6Chunk0RowsAudit &&
    tttLargeFiber44Block6Chunk0ParentMapAudit &&
    tttLargeFiber44Block6Chunk0ParentsAudit

theorem tttLargeFiber44Block6Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber44Block6Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block6Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block6Chunk0SourcesCheck_ok,
    tttLargeFiber44Block6Chunk0RowsAudit_ok,
    tttLargeFiber44Block6Chunk0ParentMapAudit_ok,
    tttLargeFiber44Block6Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block6Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
