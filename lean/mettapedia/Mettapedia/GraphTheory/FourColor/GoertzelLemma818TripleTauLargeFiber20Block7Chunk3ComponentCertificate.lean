import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 7 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block7Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block7Chunk3Sources : List Nat :=
  [   6512, 6513, 6514, 6515, 6516, 6517, 6518, 6519,
   6520, 6521, 6522, 6523, 6524, 6525, 6526, 6527]

def tttLargeFiber20Row496 : TripleComponentParentRow :=
  tripleRow 6512 6496 191 126 64 191 124 132
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

def tttLargeFiber20Row497 : TripleComponentParentRow :=
  tripleRow 6513 6497 191 126 65 191 124 133
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

def tttLargeFiber20Row498 : TripleComponentParentRow :=
  tripleRow 6514 6512 191 126 66 191 126 64
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row499 : TripleComponentParentRow :=
  tripleRow 6515 6499 191 126 67 191 124 135
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

def tttLargeFiber20Row500 : TripleComponentParentRow :=
  tripleRow 6516 6500 191 126 116 191 124 180
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row501 : TripleComponentParentRow :=
  tripleRow 6517 6501 191 126 117 191 124 181
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row502 : TripleComponentParentRow :=
  tripleRow 6518 6513 191 126 118 191 126 65
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row503 : TripleComponentParentRow :=
  tripleRow 6519 6512 191 126 119 191 126 64
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row504 : TripleComponentParentRow :=
  tripleRow 6520 6504 191 127 72 191 125 140
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

def tttLargeFiber20Row505 : TripleComponentParentRow :=
  tripleRow 6521 6505 191 127 73 191 125 141
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

def tttLargeFiber20Row506 : TripleComponentParentRow :=
  tripleRow 6522 4890 191 127 74 143 59 10
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber20Row507 : TripleComponentParentRow :=
  tripleRow 6523 4891 191 127 75 143 59 11
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber20Row508 : TripleComponentParentRow :=
  tripleRow 6524 4892 191 127 124 143 59 56
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber20Row509 : TripleComponentParentRow :=
  tripleRow 6525 4893 191 127 125 143 59 57
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber20Row510 : TripleComponentParentRow :=
  tripleRow 6526 6524 191 127 126 191 127 124
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row511 : TripleComponentParentRow :=
  tripleRow 6527 4895 191 127 127 143 59 59
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
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

def tttLargeFiber20Block7Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row496
  , tttLargeFiber20Row497
  , tttLargeFiber20Row498
  , tttLargeFiber20Row499
  , tttLargeFiber20Row500
  , tttLargeFiber20Row501
  , tttLargeFiber20Row502
  , tttLargeFiber20Row503
  , tttLargeFiber20Row504
  , tttLargeFiber20Row505
  , tttLargeFiber20Row506
  , tttLargeFiber20Row507
  , tttLargeFiber20Row508
  , tttLargeFiber20Row509
  , tttLargeFiber20Row510
  , tttLargeFiber20Row511
  ]

def tttLargeFiber20Block7Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block7Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block7Chunk3ExpectedContains row.source &&
    tttLargeFiber20Block7Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block7Chunk3SourcesCheck : Bool :=
  (tttLargeFiber20Block7Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber20Block7Chunk3Sources

theorem tttLargeFiber20Block7Chunk3SourcesCheck_ok :
    tttLargeFiber20Block7Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber20Block7Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block7Chunk3RowValid
    (listGetD tttLargeFiber20Block7Chunk3Rows i default)

def tttLargeFiber20Block7Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block7Chunk3Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block7Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block7Chunk3Sources 0 0 == 6512
      && tttLargeFiber20ParentOf 6512 == 6496
      && tttLargeFiber20ParentOf 6496 == 4864
      && tttLargeFiber20ParentOf 4864 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block7Chunk3Sources 1 0 == 6513
      && tttLargeFiber20ParentOf 6513 == 6497
      && tttLargeFiber20ParentOf 6497 == 4865
      && tttLargeFiber20ParentOf 4865 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block7Chunk3Sources 2 0 == 6514
      && tttLargeFiber20ParentOf 6514 == 6512
      && tttLargeFiber20ParentOf 6512 == 6496
      && tttLargeFiber20ParentOf 6496 == 4864
      && tttLargeFiber20ParentOf 4864 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block7Chunk3Sources 3 0 == 6515
      && tttLargeFiber20ParentOf 6515 == 6499
      && tttLargeFiber20ParentOf 6499 == 4867
      && tttLargeFiber20ParentOf 4867 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block7Chunk3Sources 4 0 == 6516
      && tttLargeFiber20ParentOf 6516 == 6500
      && tttLargeFiber20ParentOf 6500 == 4868
      && tttLargeFiber20ParentOf 4868 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block7Chunk3Sources 5 0 == 6517
      && tttLargeFiber20ParentOf 6517 == 6501
      && tttLargeFiber20ParentOf 6501 == 4869
      && tttLargeFiber20ParentOf 4869 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block7Chunk3Sources 6 0 == 6518
      && tttLargeFiber20ParentOf 6518 == 6513
      && tttLargeFiber20ParentOf 6513 == 6497
      && tttLargeFiber20ParentOf 6497 == 4865
      && tttLargeFiber20ParentOf 4865 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block7Chunk3Sources 7 0 == 6519
      && tttLargeFiber20ParentOf 6519 == 6512
      && tttLargeFiber20ParentOf 6512 == 6496
      && tttLargeFiber20ParentOf 6496 == 4864
      && tttLargeFiber20ParentOf 4864 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block7Chunk3Sources 8 0 == 6520
      && tttLargeFiber20ParentOf 6520 == 6504
      && tttLargeFiber20ParentOf 6504 == 4872
      && tttLargeFiber20ParentOf 4872 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block7Chunk3Sources 9 0 == 6521
      && tttLargeFiber20ParentOf 6521 == 6505
      && tttLargeFiber20ParentOf 6505 == 4873
      && tttLargeFiber20ParentOf 4873 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block7Chunk3Sources 10 0 == 6522
      && tttLargeFiber20ParentOf 6522 == 4890
      && tttLargeFiber20ParentOf 4890 == 4666
      && tttLargeFiber20ParentOf 4666 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block7Chunk3Sources 11 0 == 6523
      && tttLargeFiber20ParentOf 6523 == 4891
      && tttLargeFiber20ParentOf 4891 == 4667
      && tttLargeFiber20ParentOf 4667 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (5 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block7Chunk3Sources 12 0 == 6524
      && tttLargeFiber20ParentOf 6524 == 4892
      && tttLargeFiber20ParentOf 4892 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block7Chunk3Sources 13 0 == 6525
      && tttLargeFiber20ParentOf 6525 == 4893
      && tttLargeFiber20ParentOf 4893 == 4669
      && tttLargeFiber20ParentOf 4669 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block7Chunk3Sources 14 0 == 6526
      && tttLargeFiber20ParentOf 6526 == 6524
      && tttLargeFiber20ParentOf 6524 == 4892
      && tttLargeFiber20ParentOf 4892 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block7Chunk3Sources 15 0 == 6527
      && tttLargeFiber20ParentOf 6527 == 4895
      && tttLargeFiber20ParentOf 4895 == 4671
      && tttLargeFiber20ParentOf 4671 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block7Chunk3Row_0_ok :
    tttLargeFiber20Block7Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_1_ok :
    tttLargeFiber20Block7Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_2_ok :
    tttLargeFiber20Block7Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_3_ok :
    tttLargeFiber20Block7Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_4_ok :
    tttLargeFiber20Block7Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_5_ok :
    tttLargeFiber20Block7Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_6_ok :
    tttLargeFiber20Block7Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_7_ok :
    tttLargeFiber20Block7Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_8_ok :
    tttLargeFiber20Block7Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_9_ok :
    tttLargeFiber20Block7Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_10_ok :
    tttLargeFiber20Block7Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_11_ok :
    tttLargeFiber20Block7Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_12_ok :
    tttLargeFiber20Block7Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_13_ok :
    tttLargeFiber20Block7Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_14_ok :
    tttLargeFiber20Block7Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3Row_15_ok :
    tttLargeFiber20Block7Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_0_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_1_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_2_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_3_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_4_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_5_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_6_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_7_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_8_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_9_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_10_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_11_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_12_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_13_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_14_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentMap_15_ok :
    tttLargeFiber20Block7Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_0_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_1_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_2_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_3_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_4_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_5_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_6_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_7_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_8_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_9_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_10_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_11_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_12_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_13_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_14_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block7Chunk3ParentPath_15_ok :
    tttLargeFiber20Block7Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block7Chunk3RowsAudit : Bool :=
  tttLargeFiber20Block7Chunk3RowCheck 0
    && tttLargeFiber20Block7Chunk3RowCheck 1
    && tttLargeFiber20Block7Chunk3RowCheck 2
    && tttLargeFiber20Block7Chunk3RowCheck 3
    && tttLargeFiber20Block7Chunk3RowCheck 4
    && tttLargeFiber20Block7Chunk3RowCheck 5
    && tttLargeFiber20Block7Chunk3RowCheck 6
    && tttLargeFiber20Block7Chunk3RowCheck 7
    && tttLargeFiber20Block7Chunk3RowCheck 8
    && tttLargeFiber20Block7Chunk3RowCheck 9
    && tttLargeFiber20Block7Chunk3RowCheck 10
    && tttLargeFiber20Block7Chunk3RowCheck 11
    && tttLargeFiber20Block7Chunk3RowCheck 12
    && tttLargeFiber20Block7Chunk3RowCheck 13
    && tttLargeFiber20Block7Chunk3RowCheck 14
    && tttLargeFiber20Block7Chunk3RowCheck 15

theorem tttLargeFiber20Block7Chunk3RowsAudit_ok :
    tttLargeFiber20Block7Chunk3RowsAudit = true := by
  simp [tttLargeFiber20Block7Chunk3RowsAudit,
    tttLargeFiber20Block7Chunk3Row_0_ok,
    tttLargeFiber20Block7Chunk3Row_1_ok,
    tttLargeFiber20Block7Chunk3Row_2_ok,
    tttLargeFiber20Block7Chunk3Row_3_ok,
    tttLargeFiber20Block7Chunk3Row_4_ok,
    tttLargeFiber20Block7Chunk3Row_5_ok,
    tttLargeFiber20Block7Chunk3Row_6_ok,
    tttLargeFiber20Block7Chunk3Row_7_ok,
    tttLargeFiber20Block7Chunk3Row_8_ok,
    tttLargeFiber20Block7Chunk3Row_9_ok,
    tttLargeFiber20Block7Chunk3Row_10_ok,
    tttLargeFiber20Block7Chunk3Row_11_ok,
    tttLargeFiber20Block7Chunk3Row_12_ok,
    tttLargeFiber20Block7Chunk3Row_13_ok,
    tttLargeFiber20Block7Chunk3Row_14_ok,
    tttLargeFiber20Block7Chunk3Row_15_ok]

def tttLargeFiber20Block7Chunk3ParentMapAudit : Bool :=
  tttLargeFiber20Block7Chunk3ParentMapCheck 0
    && tttLargeFiber20Block7Chunk3ParentMapCheck 1
    && tttLargeFiber20Block7Chunk3ParentMapCheck 2
    && tttLargeFiber20Block7Chunk3ParentMapCheck 3
    && tttLargeFiber20Block7Chunk3ParentMapCheck 4
    && tttLargeFiber20Block7Chunk3ParentMapCheck 5
    && tttLargeFiber20Block7Chunk3ParentMapCheck 6
    && tttLargeFiber20Block7Chunk3ParentMapCheck 7
    && tttLargeFiber20Block7Chunk3ParentMapCheck 8
    && tttLargeFiber20Block7Chunk3ParentMapCheck 9
    && tttLargeFiber20Block7Chunk3ParentMapCheck 10
    && tttLargeFiber20Block7Chunk3ParentMapCheck 11
    && tttLargeFiber20Block7Chunk3ParentMapCheck 12
    && tttLargeFiber20Block7Chunk3ParentMapCheck 13
    && tttLargeFiber20Block7Chunk3ParentMapCheck 14
    && tttLargeFiber20Block7Chunk3ParentMapCheck 15

theorem tttLargeFiber20Block7Chunk3ParentMapAudit_ok :
    tttLargeFiber20Block7Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber20Block7Chunk3ParentMapAudit,
    tttLargeFiber20Block7Chunk3ParentMap_0_ok,
    tttLargeFiber20Block7Chunk3ParentMap_1_ok,
    tttLargeFiber20Block7Chunk3ParentMap_2_ok,
    tttLargeFiber20Block7Chunk3ParentMap_3_ok,
    tttLargeFiber20Block7Chunk3ParentMap_4_ok,
    tttLargeFiber20Block7Chunk3ParentMap_5_ok,
    tttLargeFiber20Block7Chunk3ParentMap_6_ok,
    tttLargeFiber20Block7Chunk3ParentMap_7_ok,
    tttLargeFiber20Block7Chunk3ParentMap_8_ok,
    tttLargeFiber20Block7Chunk3ParentMap_9_ok,
    tttLargeFiber20Block7Chunk3ParentMap_10_ok,
    tttLargeFiber20Block7Chunk3ParentMap_11_ok,
    tttLargeFiber20Block7Chunk3ParentMap_12_ok,
    tttLargeFiber20Block7Chunk3ParentMap_13_ok,
    tttLargeFiber20Block7Chunk3ParentMap_14_ok,
    tttLargeFiber20Block7Chunk3ParentMap_15_ok]

def tttLargeFiber20Block7Chunk3ParentsAudit : Bool :=
  tttLargeFiber20Block7Chunk3ParentPathCheck 0
    && tttLargeFiber20Block7Chunk3ParentPathCheck 1
    && tttLargeFiber20Block7Chunk3ParentPathCheck 2
    && tttLargeFiber20Block7Chunk3ParentPathCheck 3
    && tttLargeFiber20Block7Chunk3ParentPathCheck 4
    && tttLargeFiber20Block7Chunk3ParentPathCheck 5
    && tttLargeFiber20Block7Chunk3ParentPathCheck 6
    && tttLargeFiber20Block7Chunk3ParentPathCheck 7
    && tttLargeFiber20Block7Chunk3ParentPathCheck 8
    && tttLargeFiber20Block7Chunk3ParentPathCheck 9
    && tttLargeFiber20Block7Chunk3ParentPathCheck 10
    && tttLargeFiber20Block7Chunk3ParentPathCheck 11
    && tttLargeFiber20Block7Chunk3ParentPathCheck 12
    && tttLargeFiber20Block7Chunk3ParentPathCheck 13
    && tttLargeFiber20Block7Chunk3ParentPathCheck 14
    && tttLargeFiber20Block7Chunk3ParentPathCheck 15

theorem tttLargeFiber20Block7Chunk3ParentsAudit_ok :
    tttLargeFiber20Block7Chunk3ParentsAudit = true := by
  simp [tttLargeFiber20Block7Chunk3ParentsAudit,
    tttLargeFiber20Block7Chunk3ParentPath_0_ok,
    tttLargeFiber20Block7Chunk3ParentPath_1_ok,
    tttLargeFiber20Block7Chunk3ParentPath_2_ok,
    tttLargeFiber20Block7Chunk3ParentPath_3_ok,
    tttLargeFiber20Block7Chunk3ParentPath_4_ok,
    tttLargeFiber20Block7Chunk3ParentPath_5_ok,
    tttLargeFiber20Block7Chunk3ParentPath_6_ok,
    tttLargeFiber20Block7Chunk3ParentPath_7_ok,
    tttLargeFiber20Block7Chunk3ParentPath_8_ok,
    tttLargeFiber20Block7Chunk3ParentPath_9_ok,
    tttLargeFiber20Block7Chunk3ParentPath_10_ok,
    tttLargeFiber20Block7Chunk3ParentPath_11_ok,
    tttLargeFiber20Block7Chunk3ParentPath_12_ok,
    tttLargeFiber20Block7Chunk3ParentPath_13_ok,
    tttLargeFiber20Block7Chunk3ParentPath_14_ok,
    tttLargeFiber20Block7Chunk3ParentPath_15_ok]

def tttLargeFiber20Block7Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block7Chunk3SourcesCheck &&
    tttLargeFiber20Block7Chunk3RowsAudit &&
    tttLargeFiber20Block7Chunk3ParentMapAudit &&
    tttLargeFiber20Block7Chunk3ParentsAudit

theorem tttLargeFiber20Block7Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber20Block7Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block7Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block7Chunk3SourcesCheck_ok,
    tttLargeFiber20Block7Chunk3RowsAudit_ok,
    tttLargeFiber20Block7Chunk3ParentMapAudit_ok,
    tttLargeFiber20Block7Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block7Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
