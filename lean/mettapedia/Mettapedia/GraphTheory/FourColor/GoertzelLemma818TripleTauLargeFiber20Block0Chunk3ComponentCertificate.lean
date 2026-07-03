import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 20, block 0 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber20Block0Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Data

def tttLargeFiber20Block0Chunk3Sources : List Nat :=
  [   4688, 4689, 4690, 4691, 4692, 4693, 4694, 4695,
   4696, 4697, 4698, 4699, 4700, 4701, 4702, 4703]

def tttLargeFiber20Row48 : TripleComponentParentRow :=
  tripleRow 4688 4672 140 166 64 140 164 132
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

def tttLargeFiber20Row49 : TripleComponentParentRow :=
  tripleRow 4689 4673 140 166 65 140 164 133
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

def tttLargeFiber20Row50 : TripleComponentParentRow :=
  tripleRow 4690 4688 140 166 66 140 166 64
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row51 : TripleComponentParentRow :=
  tripleRow 4691 4675 140 166 67 140 164 135
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

def tttLargeFiber20Row52 : TripleComponentParentRow :=
  tripleRow 4692 4676 140 166 116 140 164 180
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row53 : TripleComponentParentRow :=
  tripleRow 4693 4677 140 166 117 140 164 181
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber20Row54 : TripleComponentParentRow :=
  tripleRow 4694 4689 140 166 118 140 166 65
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber20Row55 : TripleComponentParentRow :=
  tripleRow 4695 4688 140 166 119 140 166 64
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber20Row56 : TripleComponentParentRow :=
  tripleRow 4696 4680 140 167 72 140 165 140
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

def tttLargeFiber20Row57 : TripleComponentParentRow :=
  tripleRow 4697 4681 140 167 73 140 165 141
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

def tttLargeFiber20Row58 : TripleComponentParentRow :=
  tripleRow 4698 4666 140 167 74 140 151 10
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row59 : TripleComponentParentRow :=
  tripleRow 4699 4667 140 167 75 140 151 11
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber20Row60 : TripleComponentParentRow :=
  tripleRow 4700 4668 140 167 124 140 151 56
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

def tttLargeFiber20Row61 : TripleComponentParentRow :=
  tripleRow 4701 4669 140 167 125 140 151 57
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

def tttLargeFiber20Row62 : TripleComponentParentRow :=
  tripleRow 4702 4700 140 167 126 140 167 124
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Row63 : TripleComponentParentRow :=
  tripleRow 4703 4671 140 167 127 140 151 59
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber20Block0Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber20Row48
  , tttLargeFiber20Row49
  , tttLargeFiber20Row50
  , tttLargeFiber20Row51
  , tttLargeFiber20Row52
  , tttLargeFiber20Row53
  , tttLargeFiber20Row54
  , tttLargeFiber20Row55
  , tttLargeFiber20Row56
  , tttLargeFiber20Row57
  , tttLargeFiber20Row58
  , tttLargeFiber20Row59
  , tttLargeFiber20Row60
  , tttLargeFiber20Row61
  , tttLargeFiber20Row62
  , tttLargeFiber20Row63
  ]

def tttLargeFiber20Block0Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4640 <= i) && decide (i < 4896)) ||
    (decide (6272 <= i) && decide (i < 6528))

def tttLargeFiber20Block0Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber20Block0Chunk3ExpectedContains row.source &&
    tttLargeFiber20Block0Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber20Key &&
          chainInputKey tttWord t == tttLargeFiber20Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber20Block0Chunk3SourcesCheck : Bool :=
  (tttLargeFiber20Block0Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber20Block0Chunk3Sources

theorem tttLargeFiber20Block0Chunk3SourcesCheck_ok :
    tttLargeFiber20Block0Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber20Block0Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber20Block0Chunk3RowValid
    (listGetD tttLargeFiber20Block0Chunk3Rows i default)

def tttLargeFiber20Block0Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber20Block0Chunk3Rows i default
  row.parent == tttLargeFiber20ParentOf row.source

def tttLargeFiber20Block0Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber20Block0Chunk3Sources 0 0 == 4688
      && tttLargeFiber20ParentOf 4688 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 1 => listGetD tttLargeFiber20Block0Chunk3Sources 1 0 == 4689
      && tttLargeFiber20ParentOf 4689 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 2 => listGetD tttLargeFiber20Block0Chunk3Sources 2 0 == 4690
      && tttLargeFiber20ParentOf 4690 == 4688
      && tttLargeFiber20ParentOf 4688 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 3 => listGetD tttLargeFiber20Block0Chunk3Sources 3 0 == 4691
      && tttLargeFiber20ParentOf 4691 == 4675
      && tttLargeFiber20ParentOf 4675 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 4 => listGetD tttLargeFiber20Block0Chunk3Sources 4 0 == 4692
      && tttLargeFiber20ParentOf 4692 == 4676
      && tttLargeFiber20ParentOf 4676 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 5 => listGetD tttLargeFiber20Block0Chunk3Sources 5 0 == 4693
      && tttLargeFiber20ParentOf 4693 == 4677
      && tttLargeFiber20ParentOf 4677 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 6 => listGetD tttLargeFiber20Block0Chunk3Sources 6 0 == 4694
      && tttLargeFiber20ParentOf 4694 == 4689
      && tttLargeFiber20ParentOf 4689 == 4673
      && tttLargeFiber20ParentOf 4673 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 7 => listGetD tttLargeFiber20Block0Chunk3Sources 7 0 == 4695
      && tttLargeFiber20ParentOf 4695 == 4688
      && tttLargeFiber20ParentOf 4688 == 4672
      && tttLargeFiber20ParentOf 4672 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 8 => listGetD tttLargeFiber20Block0Chunk3Sources 8 0 == 4696
      && tttLargeFiber20ParentOf 4696 == 4680
      && tttLargeFiber20ParentOf 4680 == 4648
      && tttLargeFiber20ParentOf 4648 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 9 => listGetD tttLargeFiber20Block0Chunk3Sources 9 0 == 4697
      && tttLargeFiber20ParentOf 4697 == 4681
      && tttLargeFiber20ParentOf 4681 == 4649
      && tttLargeFiber20ParentOf 4649 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 10 => listGetD tttLargeFiber20Block0Chunk3Sources 10 0 == 4698
      && tttLargeFiber20ParentOf 4698 == 4666
      && tttLargeFiber20ParentOf 4666 == 4644
      && tttLargeFiber20ParentOf 4644 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 11 => listGetD tttLargeFiber20Block0Chunk3Sources 11 0 == 4699
      && tttLargeFiber20ParentOf 4699 == 4667
      && tttLargeFiber20ParentOf 4667 == 4645
      && tttLargeFiber20ParentOf 4645 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (4 <= tttLargeFiber20MaxParentDepth)
  | 12 => listGetD tttLargeFiber20Block0Chunk3Sources 12 0 == 4700
      && tttLargeFiber20ParentOf 4700 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (2 <= tttLargeFiber20MaxParentDepth)
  | 13 => listGetD tttLargeFiber20Block0Chunk3Sources 13 0 == 4701
      && tttLargeFiber20ParentOf 4701 == 4669
      && tttLargeFiber20ParentOf 4669 == 4641
      && tttLargeFiber20ParentOf 4641 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 14 => listGetD tttLargeFiber20Block0Chunk3Sources 14 0 == 4702
      && tttLargeFiber20ParentOf 4702 == 4700
      && tttLargeFiber20ParentOf 4700 == 4668
      && tttLargeFiber20ParentOf 4668 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | 15 => listGetD tttLargeFiber20Block0Chunk3Sources 15 0 == 4703
      && tttLargeFiber20ParentOf 4703 == 4671
      && tttLargeFiber20ParentOf 4671 == 4643
      && tttLargeFiber20ParentOf 4643 == 4640
      && 4640 == tttLargeFiber20Root
      && decide (3 <= tttLargeFiber20MaxParentDepth)
  | _ => false

theorem tttLargeFiber20Block0Chunk3Row_0_ok :
    tttLargeFiber20Block0Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_1_ok :
    tttLargeFiber20Block0Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_2_ok :
    tttLargeFiber20Block0Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_3_ok :
    tttLargeFiber20Block0Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_4_ok :
    tttLargeFiber20Block0Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_5_ok :
    tttLargeFiber20Block0Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_6_ok :
    tttLargeFiber20Block0Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_7_ok :
    tttLargeFiber20Block0Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_8_ok :
    tttLargeFiber20Block0Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_9_ok :
    tttLargeFiber20Block0Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_10_ok :
    tttLargeFiber20Block0Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_11_ok :
    tttLargeFiber20Block0Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_12_ok :
    tttLargeFiber20Block0Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_13_ok :
    tttLargeFiber20Block0Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_14_ok :
    tttLargeFiber20Block0Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3Row_15_ok :
    tttLargeFiber20Block0Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_0_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_1_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_2_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_3_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_4_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_5_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_6_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_7_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_8_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_9_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_10_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_11_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_12_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_13_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_14_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentMap_15_ok :
    tttLargeFiber20Block0Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_0_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_1_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_2_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_3_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_4_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_5_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_6_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_7_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_8_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_9_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_10_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_11_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_12_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_13_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_14_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber20Block0Chunk3ParentPath_15_ok :
    tttLargeFiber20Block0Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber20Block0Chunk3RowsAudit : Bool :=
  tttLargeFiber20Block0Chunk3RowCheck 0
    && tttLargeFiber20Block0Chunk3RowCheck 1
    && tttLargeFiber20Block0Chunk3RowCheck 2
    && tttLargeFiber20Block0Chunk3RowCheck 3
    && tttLargeFiber20Block0Chunk3RowCheck 4
    && tttLargeFiber20Block0Chunk3RowCheck 5
    && tttLargeFiber20Block0Chunk3RowCheck 6
    && tttLargeFiber20Block0Chunk3RowCheck 7
    && tttLargeFiber20Block0Chunk3RowCheck 8
    && tttLargeFiber20Block0Chunk3RowCheck 9
    && tttLargeFiber20Block0Chunk3RowCheck 10
    && tttLargeFiber20Block0Chunk3RowCheck 11
    && tttLargeFiber20Block0Chunk3RowCheck 12
    && tttLargeFiber20Block0Chunk3RowCheck 13
    && tttLargeFiber20Block0Chunk3RowCheck 14
    && tttLargeFiber20Block0Chunk3RowCheck 15

theorem tttLargeFiber20Block0Chunk3RowsAudit_ok :
    tttLargeFiber20Block0Chunk3RowsAudit = true := by
  simp [tttLargeFiber20Block0Chunk3RowsAudit,
    tttLargeFiber20Block0Chunk3Row_0_ok,
    tttLargeFiber20Block0Chunk3Row_1_ok,
    tttLargeFiber20Block0Chunk3Row_2_ok,
    tttLargeFiber20Block0Chunk3Row_3_ok,
    tttLargeFiber20Block0Chunk3Row_4_ok,
    tttLargeFiber20Block0Chunk3Row_5_ok,
    tttLargeFiber20Block0Chunk3Row_6_ok,
    tttLargeFiber20Block0Chunk3Row_7_ok,
    tttLargeFiber20Block0Chunk3Row_8_ok,
    tttLargeFiber20Block0Chunk3Row_9_ok,
    tttLargeFiber20Block0Chunk3Row_10_ok,
    tttLargeFiber20Block0Chunk3Row_11_ok,
    tttLargeFiber20Block0Chunk3Row_12_ok,
    tttLargeFiber20Block0Chunk3Row_13_ok,
    tttLargeFiber20Block0Chunk3Row_14_ok,
    tttLargeFiber20Block0Chunk3Row_15_ok]

def tttLargeFiber20Block0Chunk3ParentMapAudit : Bool :=
  tttLargeFiber20Block0Chunk3ParentMapCheck 0
    && tttLargeFiber20Block0Chunk3ParentMapCheck 1
    && tttLargeFiber20Block0Chunk3ParentMapCheck 2
    && tttLargeFiber20Block0Chunk3ParentMapCheck 3
    && tttLargeFiber20Block0Chunk3ParentMapCheck 4
    && tttLargeFiber20Block0Chunk3ParentMapCheck 5
    && tttLargeFiber20Block0Chunk3ParentMapCheck 6
    && tttLargeFiber20Block0Chunk3ParentMapCheck 7
    && tttLargeFiber20Block0Chunk3ParentMapCheck 8
    && tttLargeFiber20Block0Chunk3ParentMapCheck 9
    && tttLargeFiber20Block0Chunk3ParentMapCheck 10
    && tttLargeFiber20Block0Chunk3ParentMapCheck 11
    && tttLargeFiber20Block0Chunk3ParentMapCheck 12
    && tttLargeFiber20Block0Chunk3ParentMapCheck 13
    && tttLargeFiber20Block0Chunk3ParentMapCheck 14
    && tttLargeFiber20Block0Chunk3ParentMapCheck 15

theorem tttLargeFiber20Block0Chunk3ParentMapAudit_ok :
    tttLargeFiber20Block0Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber20Block0Chunk3ParentMapAudit,
    tttLargeFiber20Block0Chunk3ParentMap_0_ok,
    tttLargeFiber20Block0Chunk3ParentMap_1_ok,
    tttLargeFiber20Block0Chunk3ParentMap_2_ok,
    tttLargeFiber20Block0Chunk3ParentMap_3_ok,
    tttLargeFiber20Block0Chunk3ParentMap_4_ok,
    tttLargeFiber20Block0Chunk3ParentMap_5_ok,
    tttLargeFiber20Block0Chunk3ParentMap_6_ok,
    tttLargeFiber20Block0Chunk3ParentMap_7_ok,
    tttLargeFiber20Block0Chunk3ParentMap_8_ok,
    tttLargeFiber20Block0Chunk3ParentMap_9_ok,
    tttLargeFiber20Block0Chunk3ParentMap_10_ok,
    tttLargeFiber20Block0Chunk3ParentMap_11_ok,
    tttLargeFiber20Block0Chunk3ParentMap_12_ok,
    tttLargeFiber20Block0Chunk3ParentMap_13_ok,
    tttLargeFiber20Block0Chunk3ParentMap_14_ok,
    tttLargeFiber20Block0Chunk3ParentMap_15_ok]

def tttLargeFiber20Block0Chunk3ParentsAudit : Bool :=
  tttLargeFiber20Block0Chunk3ParentPathCheck 0
    && tttLargeFiber20Block0Chunk3ParentPathCheck 1
    && tttLargeFiber20Block0Chunk3ParentPathCheck 2
    && tttLargeFiber20Block0Chunk3ParentPathCheck 3
    && tttLargeFiber20Block0Chunk3ParentPathCheck 4
    && tttLargeFiber20Block0Chunk3ParentPathCheck 5
    && tttLargeFiber20Block0Chunk3ParentPathCheck 6
    && tttLargeFiber20Block0Chunk3ParentPathCheck 7
    && tttLargeFiber20Block0Chunk3ParentPathCheck 8
    && tttLargeFiber20Block0Chunk3ParentPathCheck 9
    && tttLargeFiber20Block0Chunk3ParentPathCheck 10
    && tttLargeFiber20Block0Chunk3ParentPathCheck 11
    && tttLargeFiber20Block0Chunk3ParentPathCheck 12
    && tttLargeFiber20Block0Chunk3ParentPathCheck 13
    && tttLargeFiber20Block0Chunk3ParentPathCheck 14
    && tttLargeFiber20Block0Chunk3ParentPathCheck 15

theorem tttLargeFiber20Block0Chunk3ParentsAudit_ok :
    tttLargeFiber20Block0Chunk3ParentsAudit = true := by
  simp [tttLargeFiber20Block0Chunk3ParentsAudit,
    tttLargeFiber20Block0Chunk3ParentPath_0_ok,
    tttLargeFiber20Block0Chunk3ParentPath_1_ok,
    tttLargeFiber20Block0Chunk3ParentPath_2_ok,
    tttLargeFiber20Block0Chunk3ParentPath_3_ok,
    tttLargeFiber20Block0Chunk3ParentPath_4_ok,
    tttLargeFiber20Block0Chunk3ParentPath_5_ok,
    tttLargeFiber20Block0Chunk3ParentPath_6_ok,
    tttLargeFiber20Block0Chunk3ParentPath_7_ok,
    tttLargeFiber20Block0Chunk3ParentPath_8_ok,
    tttLargeFiber20Block0Chunk3ParentPath_9_ok,
    tttLargeFiber20Block0Chunk3ParentPath_10_ok,
    tttLargeFiber20Block0Chunk3ParentPath_11_ok,
    tttLargeFiber20Block0Chunk3ParentPath_12_ok,
    tttLargeFiber20Block0Chunk3ParentPath_13_ok,
    tttLargeFiber20Block0Chunk3ParentPath_14_ok,
    tttLargeFiber20Block0Chunk3ParentPath_15_ok]

def tttLargeFiber20Block0Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber20CountsAudit &&
    tttLargeFiber20Block0Chunk3SourcesCheck &&
    tttLargeFiber20Block0Chunk3RowsAudit &&
    tttLargeFiber20Block0Chunk3ParentMapAudit &&
    tttLargeFiber20Block0Chunk3ParentsAudit

theorem tttLargeFiber20Block0Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber20Block0Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber20Block0Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber20CountsAudit_ok,
    tttLargeFiber20Block0Chunk3SourcesCheck_ok,
    tttLargeFiber20Block0Chunk3RowsAudit_ok,
    tttLargeFiber20Block0Chunk3ParentMapAudit_ok,
    tttLargeFiber20Block0Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber20Block0Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
