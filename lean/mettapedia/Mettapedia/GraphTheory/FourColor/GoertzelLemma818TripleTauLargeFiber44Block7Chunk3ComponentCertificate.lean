import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 7 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block7Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block7Chunk3Sources : List Nat :=
  [   5696, 5697, 5698, 5699, 5700, 5701, 5702, 5703,
   5704, 5705, 5706, 5707, 5708, 5709, 5710, 5711]

def tttLargeFiber44Row496 : TripleComponentParentRow :=
  tripleRow 5696 5680 167 126 64 167 124 132
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

def tttLargeFiber44Row497 : TripleComponentParentRow :=
  tripleRow 5697 5681 167 126 65 167 124 133
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

def tttLargeFiber44Row498 : TripleComponentParentRow :=
  tripleRow 5698 5696 167 126 66 167 126 64
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row499 : TripleComponentParentRow :=
  tripleRow 5699 5683 167 126 67 167 124 135
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

def tttLargeFiber44Row500 : TripleComponentParentRow :=
  tripleRow 5700 5684 167 126 116 167 124 180
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row501 : TripleComponentParentRow :=
  tripleRow 5701 5685 167 126 117 167 124 181
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row502 : TripleComponentParentRow :=
  tripleRow 5702 5697 167 126 118 167 126 65
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row503 : TripleComponentParentRow :=
  tripleRow 5703 5696 167 126 119 167 126 64
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Row504 : TripleComponentParentRow :=
  tripleRow 5704 5688 167 127 72 167 125 140
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

def tttLargeFiber44Row505 : TripleComponentParentRow :=
  tripleRow 5705 5689 167 127 73 167 125 141
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

def tttLargeFiber44Row506 : TripleComponentParentRow :=
  tripleRow 5706 5162 167 127 74 151 59 10
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

def tttLargeFiber44Row507 : TripleComponentParentRow :=
  tripleRow 5707 5163 167 127 75 151 59 11
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

def tttLargeFiber44Row508 : TripleComponentParentRow :=
  tripleRow 5708 5164 167 127 124 151 59 56
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

def tttLargeFiber44Row509 : TripleComponentParentRow :=
  tripleRow 5709 5165 167 127 125 151 59 57
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

def tttLargeFiber44Row510 : TripleComponentParentRow :=
  tripleRow 5710 5708 167 127 126 167 127 124
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row511 : TripleComponentParentRow :=
  tripleRow 5711 5167 167 127 127 151 59 59
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

def tttLargeFiber44Block7Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row496
  , tttLargeFiber44Row497
  , tttLargeFiber44Row498
  , tttLargeFiber44Row499
  , tttLargeFiber44Row500
  , tttLargeFiber44Row501
  , tttLargeFiber44Row502
  , tttLargeFiber44Row503
  , tttLargeFiber44Row504
  , tttLargeFiber44Row505
  , tttLargeFiber44Row506
  , tttLargeFiber44Row507
  , tttLargeFiber44Row508
  , tttLargeFiber44Row509
  , tttLargeFiber44Row510
  , tttLargeFiber44Row511
  ]

def tttLargeFiber44Block7Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block7Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block7Chunk3ExpectedContains row.source &&
    tttLargeFiber44Block7Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block7Chunk3SourcesCheck : Bool :=
  (tttLargeFiber44Block7Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber44Block7Chunk3Sources

theorem tttLargeFiber44Block7Chunk3SourcesCheck_ok :
    tttLargeFiber44Block7Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber44Block7Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block7Chunk3RowValid
    (listGetD tttLargeFiber44Block7Chunk3Rows i default)

def tttLargeFiber44Block7Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block7Chunk3Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block7Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block7Chunk3Sources 0 0 == 5696
      && tttLargeFiber44ParentOf 5696 == 5680
      && tttLargeFiber44ParentOf 5680 == 5136
      && tttLargeFiber44ParentOf 5136 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block7Chunk3Sources 1 0 == 5697
      && tttLargeFiber44ParentOf 5697 == 5681
      && tttLargeFiber44ParentOf 5681 == 5137
      && tttLargeFiber44ParentOf 5137 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block7Chunk3Sources 2 0 == 5698
      && tttLargeFiber44ParentOf 5698 == 5696
      && tttLargeFiber44ParentOf 5696 == 5680
      && tttLargeFiber44ParentOf 5680 == 5136
      && tttLargeFiber44ParentOf 5136 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block7Chunk3Sources 3 0 == 5699
      && tttLargeFiber44ParentOf 5699 == 5683
      && tttLargeFiber44ParentOf 5683 == 5139
      && tttLargeFiber44ParentOf 5139 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block7Chunk3Sources 4 0 == 5700
      && tttLargeFiber44ParentOf 5700 == 5684
      && tttLargeFiber44ParentOf 5684 == 5140
      && tttLargeFiber44ParentOf 5140 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block7Chunk3Sources 5 0 == 5701
      && tttLargeFiber44ParentOf 5701 == 5685
      && tttLargeFiber44ParentOf 5685 == 5141
      && tttLargeFiber44ParentOf 5141 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block7Chunk3Sources 6 0 == 5702
      && tttLargeFiber44ParentOf 5702 == 5697
      && tttLargeFiber44ParentOf 5697 == 5681
      && tttLargeFiber44ParentOf 5681 == 5137
      && tttLargeFiber44ParentOf 5137 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block7Chunk3Sources 7 0 == 5703
      && tttLargeFiber44ParentOf 5703 == 5696
      && tttLargeFiber44ParentOf 5696 == 5680
      && tttLargeFiber44ParentOf 5680 == 5136
      && tttLargeFiber44ParentOf 5136 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block7Chunk3Sources 8 0 == 5704
      && tttLargeFiber44ParentOf 5704 == 5688
      && tttLargeFiber44ParentOf 5688 == 5144
      && tttLargeFiber44ParentOf 5144 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block7Chunk3Sources 9 0 == 5705
      && tttLargeFiber44ParentOf 5705 == 5689
      && tttLargeFiber44ParentOf 5689 == 5145
      && tttLargeFiber44ParentOf 5145 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block7Chunk3Sources 10 0 == 5706
      && tttLargeFiber44ParentOf 5706 == 5162
      && tttLargeFiber44ParentOf 5162 == 4938
      && tttLargeFiber44ParentOf 4938 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block7Chunk3Sources 11 0 == 5707
      && tttLargeFiber44ParentOf 5707 == 5163
      && tttLargeFiber44ParentOf 5163 == 4939
      && tttLargeFiber44ParentOf 4939 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block7Chunk3Sources 12 0 == 5708
      && tttLargeFiber44ParentOf 5708 == 5164
      && tttLargeFiber44ParentOf 5164 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block7Chunk3Sources 13 0 == 5709
      && tttLargeFiber44ParentOf 5709 == 5165
      && tttLargeFiber44ParentOf 5165 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block7Chunk3Sources 14 0 == 5710
      && tttLargeFiber44ParentOf 5710 == 5708
      && tttLargeFiber44ParentOf 5708 == 5164
      && tttLargeFiber44ParentOf 5164 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block7Chunk3Sources 15 0 == 5711
      && tttLargeFiber44ParentOf 5711 == 5167
      && tttLargeFiber44ParentOf 5167 == 4943
      && tttLargeFiber44ParentOf 4943 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block7Chunk3Row_0_ok :
    tttLargeFiber44Block7Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_1_ok :
    tttLargeFiber44Block7Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_2_ok :
    tttLargeFiber44Block7Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_3_ok :
    tttLargeFiber44Block7Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_4_ok :
    tttLargeFiber44Block7Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_5_ok :
    tttLargeFiber44Block7Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_6_ok :
    tttLargeFiber44Block7Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_7_ok :
    tttLargeFiber44Block7Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_8_ok :
    tttLargeFiber44Block7Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_9_ok :
    tttLargeFiber44Block7Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_10_ok :
    tttLargeFiber44Block7Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_11_ok :
    tttLargeFiber44Block7Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_12_ok :
    tttLargeFiber44Block7Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_13_ok :
    tttLargeFiber44Block7Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_14_ok :
    tttLargeFiber44Block7Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3Row_15_ok :
    tttLargeFiber44Block7Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_0_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_1_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_2_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_3_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_4_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_5_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_6_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_7_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_8_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_9_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_10_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_11_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_12_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_13_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_14_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentMap_15_ok :
    tttLargeFiber44Block7Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_0_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_1_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_2_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_3_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_4_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_5_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_6_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_7_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_8_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_9_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_10_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_11_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_12_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_13_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_14_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block7Chunk3ParentPath_15_ok :
    tttLargeFiber44Block7Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block7Chunk3RowsAudit : Bool :=
  tttLargeFiber44Block7Chunk3RowCheck 0
    && tttLargeFiber44Block7Chunk3RowCheck 1
    && tttLargeFiber44Block7Chunk3RowCheck 2
    && tttLargeFiber44Block7Chunk3RowCheck 3
    && tttLargeFiber44Block7Chunk3RowCheck 4
    && tttLargeFiber44Block7Chunk3RowCheck 5
    && tttLargeFiber44Block7Chunk3RowCheck 6
    && tttLargeFiber44Block7Chunk3RowCheck 7
    && tttLargeFiber44Block7Chunk3RowCheck 8
    && tttLargeFiber44Block7Chunk3RowCheck 9
    && tttLargeFiber44Block7Chunk3RowCheck 10
    && tttLargeFiber44Block7Chunk3RowCheck 11
    && tttLargeFiber44Block7Chunk3RowCheck 12
    && tttLargeFiber44Block7Chunk3RowCheck 13
    && tttLargeFiber44Block7Chunk3RowCheck 14
    && tttLargeFiber44Block7Chunk3RowCheck 15

theorem tttLargeFiber44Block7Chunk3RowsAudit_ok :
    tttLargeFiber44Block7Chunk3RowsAudit = true := by
  simp [tttLargeFiber44Block7Chunk3RowsAudit,
    tttLargeFiber44Block7Chunk3Row_0_ok,
    tttLargeFiber44Block7Chunk3Row_1_ok,
    tttLargeFiber44Block7Chunk3Row_2_ok,
    tttLargeFiber44Block7Chunk3Row_3_ok,
    tttLargeFiber44Block7Chunk3Row_4_ok,
    tttLargeFiber44Block7Chunk3Row_5_ok,
    tttLargeFiber44Block7Chunk3Row_6_ok,
    tttLargeFiber44Block7Chunk3Row_7_ok,
    tttLargeFiber44Block7Chunk3Row_8_ok,
    tttLargeFiber44Block7Chunk3Row_9_ok,
    tttLargeFiber44Block7Chunk3Row_10_ok,
    tttLargeFiber44Block7Chunk3Row_11_ok,
    tttLargeFiber44Block7Chunk3Row_12_ok,
    tttLargeFiber44Block7Chunk3Row_13_ok,
    tttLargeFiber44Block7Chunk3Row_14_ok,
    tttLargeFiber44Block7Chunk3Row_15_ok]

def tttLargeFiber44Block7Chunk3ParentMapAudit : Bool :=
  tttLargeFiber44Block7Chunk3ParentMapCheck 0
    && tttLargeFiber44Block7Chunk3ParentMapCheck 1
    && tttLargeFiber44Block7Chunk3ParentMapCheck 2
    && tttLargeFiber44Block7Chunk3ParentMapCheck 3
    && tttLargeFiber44Block7Chunk3ParentMapCheck 4
    && tttLargeFiber44Block7Chunk3ParentMapCheck 5
    && tttLargeFiber44Block7Chunk3ParentMapCheck 6
    && tttLargeFiber44Block7Chunk3ParentMapCheck 7
    && tttLargeFiber44Block7Chunk3ParentMapCheck 8
    && tttLargeFiber44Block7Chunk3ParentMapCheck 9
    && tttLargeFiber44Block7Chunk3ParentMapCheck 10
    && tttLargeFiber44Block7Chunk3ParentMapCheck 11
    && tttLargeFiber44Block7Chunk3ParentMapCheck 12
    && tttLargeFiber44Block7Chunk3ParentMapCheck 13
    && tttLargeFiber44Block7Chunk3ParentMapCheck 14
    && tttLargeFiber44Block7Chunk3ParentMapCheck 15

theorem tttLargeFiber44Block7Chunk3ParentMapAudit_ok :
    tttLargeFiber44Block7Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber44Block7Chunk3ParentMapAudit,
    tttLargeFiber44Block7Chunk3ParentMap_0_ok,
    tttLargeFiber44Block7Chunk3ParentMap_1_ok,
    tttLargeFiber44Block7Chunk3ParentMap_2_ok,
    tttLargeFiber44Block7Chunk3ParentMap_3_ok,
    tttLargeFiber44Block7Chunk3ParentMap_4_ok,
    tttLargeFiber44Block7Chunk3ParentMap_5_ok,
    tttLargeFiber44Block7Chunk3ParentMap_6_ok,
    tttLargeFiber44Block7Chunk3ParentMap_7_ok,
    tttLargeFiber44Block7Chunk3ParentMap_8_ok,
    tttLargeFiber44Block7Chunk3ParentMap_9_ok,
    tttLargeFiber44Block7Chunk3ParentMap_10_ok,
    tttLargeFiber44Block7Chunk3ParentMap_11_ok,
    tttLargeFiber44Block7Chunk3ParentMap_12_ok,
    tttLargeFiber44Block7Chunk3ParentMap_13_ok,
    tttLargeFiber44Block7Chunk3ParentMap_14_ok,
    tttLargeFiber44Block7Chunk3ParentMap_15_ok]

def tttLargeFiber44Block7Chunk3ParentsAudit : Bool :=
  tttLargeFiber44Block7Chunk3ParentPathCheck 0
    && tttLargeFiber44Block7Chunk3ParentPathCheck 1
    && tttLargeFiber44Block7Chunk3ParentPathCheck 2
    && tttLargeFiber44Block7Chunk3ParentPathCheck 3
    && tttLargeFiber44Block7Chunk3ParentPathCheck 4
    && tttLargeFiber44Block7Chunk3ParentPathCheck 5
    && tttLargeFiber44Block7Chunk3ParentPathCheck 6
    && tttLargeFiber44Block7Chunk3ParentPathCheck 7
    && tttLargeFiber44Block7Chunk3ParentPathCheck 8
    && tttLargeFiber44Block7Chunk3ParentPathCheck 9
    && tttLargeFiber44Block7Chunk3ParentPathCheck 10
    && tttLargeFiber44Block7Chunk3ParentPathCheck 11
    && tttLargeFiber44Block7Chunk3ParentPathCheck 12
    && tttLargeFiber44Block7Chunk3ParentPathCheck 13
    && tttLargeFiber44Block7Chunk3ParentPathCheck 14
    && tttLargeFiber44Block7Chunk3ParentPathCheck 15

theorem tttLargeFiber44Block7Chunk3ParentsAudit_ok :
    tttLargeFiber44Block7Chunk3ParentsAudit = true := by
  simp [tttLargeFiber44Block7Chunk3ParentsAudit,
    tttLargeFiber44Block7Chunk3ParentPath_0_ok,
    tttLargeFiber44Block7Chunk3ParentPath_1_ok,
    tttLargeFiber44Block7Chunk3ParentPath_2_ok,
    tttLargeFiber44Block7Chunk3ParentPath_3_ok,
    tttLargeFiber44Block7Chunk3ParentPath_4_ok,
    tttLargeFiber44Block7Chunk3ParentPath_5_ok,
    tttLargeFiber44Block7Chunk3ParentPath_6_ok,
    tttLargeFiber44Block7Chunk3ParentPath_7_ok,
    tttLargeFiber44Block7Chunk3ParentPath_8_ok,
    tttLargeFiber44Block7Chunk3ParentPath_9_ok,
    tttLargeFiber44Block7Chunk3ParentPath_10_ok,
    tttLargeFiber44Block7Chunk3ParentPath_11_ok,
    tttLargeFiber44Block7Chunk3ParentPath_12_ok,
    tttLargeFiber44Block7Chunk3ParentPath_13_ok,
    tttLargeFiber44Block7Chunk3ParentPath_14_ok,
    tttLargeFiber44Block7Chunk3ParentPath_15_ok]

def tttLargeFiber44Block7Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block7Chunk3SourcesCheck &&
    tttLargeFiber44Block7Chunk3RowsAudit &&
    tttLargeFiber44Block7Chunk3ParentMapAudit &&
    tttLargeFiber44Block7Chunk3ParentsAudit

theorem tttLargeFiber44Block7Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber44Block7Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block7Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block7Chunk3SourcesCheck_ok,
    tttLargeFiber44Block7Chunk3RowsAudit_ok,
    tttLargeFiber44Block7Chunk3ParentMapAudit_ok,
    tttLargeFiber44Block7Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block7Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
