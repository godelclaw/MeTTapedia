import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 6 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block6Chunk1Sources : List Nat :=
  [   1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783,
   1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]

def tttLargeFiber30Row400 : TripleComponentParentRow :=
  tripleRow 1776 144 50 2 16 2 18 16
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row401 : TripleComponentParentRow :=
  tripleRow 1777 145 50 2 17 2 18 17
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row402 : TripleComponentParentRow :=
  tripleRow 1778 146 50 2 18 2 18 18
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row403 : TripleComponentParentRow :=
  tripleRow 1779 147 50 2 19 2 18 19
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row404 : TripleComponentParentRow :=
  tripleRow 1780 148 50 2 32 2 18 32
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row405 : TripleComponentParentRow :=
  tripleRow 1781 149 50 2 33 2 18 33
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row406 : TripleComponentParentRow :=
  tripleRow 1782 150 50 2 34 2 18 34
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row407 : TripleComponentParentRow :=
  tripleRow 1783 151 50 2 35 2 18 35
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row408 : TripleComponentParentRow :=
  tripleRow 1784 152 50 3 24 2 19 24
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row409 : TripleComponentParentRow :=
  tripleRow 1785 153 50 3 25 2 19 25
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row410 : TripleComponentParentRow :=
  tripleRow 1786 154 50 3 26 2 19 26
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row411 : TripleComponentParentRow :=
  tripleRow 1787 155 50 3 27 2 19 27
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row412 : TripleComponentParentRow :=
  tripleRow 1788 156 50 3 40 2 19 40
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row413 : TripleComponentParentRow :=
  tripleRow 1789 157 50 3 41 2 19 41
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row414 : TripleComponentParentRow :=
  tripleRow 1790 158 50 3 42 2 19 42
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row415 : TripleComponentParentRow :=
  tripleRow 1791 159 50 3 43 2 19 43
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row400
  , tttLargeFiber30Row401
  , tttLargeFiber30Row402
  , tttLargeFiber30Row403
  , tttLargeFiber30Row404
  , tttLargeFiber30Row405
  , tttLargeFiber30Row406
  , tttLargeFiber30Row407
  , tttLargeFiber30Row408
  , tttLargeFiber30Row409
  , tttLargeFiber30Row410
  , tttLargeFiber30Row411
  , tttLargeFiber30Row412
  , tttLargeFiber30Row413
  , tttLargeFiber30Row414
  , tttLargeFiber30Row415
  ]

def tttLargeFiber30Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber30Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber30Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber30Block6Chunk1Sources

theorem tttLargeFiber30Block6Chunk1SourcesCheck_ok :
    tttLargeFiber30Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber30Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block6Chunk1RowValid
    (listGetD tttLargeFiber30Block6Chunk1Rows i default)

def tttLargeFiber30Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block6Chunk1Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block6Chunk1Sources 0 0 == 1776
      && tttLargeFiber30ParentOf 1776 == 144
      && tttLargeFiber30ParentOf 144 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block6Chunk1Sources 1 0 == 1777
      && tttLargeFiber30ParentOf 1777 == 145
      && tttLargeFiber30ParentOf 145 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block6Chunk1Sources 2 0 == 1778
      && tttLargeFiber30ParentOf 1778 == 146
      && tttLargeFiber30ParentOf 146 == 18
      && tttLargeFiber30ParentOf 18 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block6Chunk1Sources 3 0 == 1779
      && tttLargeFiber30ParentOf 1779 == 147
      && tttLargeFiber30ParentOf 147 == 19
      && tttLargeFiber30ParentOf 19 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block6Chunk1Sources 4 0 == 1780
      && tttLargeFiber30ParentOf 1780 == 148
      && tttLargeFiber30ParentOf 148 == 20
      && tttLargeFiber30ParentOf 20 == 16
      && tttLargeFiber30ParentOf 16 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block6Chunk1Sources 5 0 == 1781
      && tttLargeFiber30ParentOf 1781 == 149
      && tttLargeFiber30ParentOf 149 == 21
      && tttLargeFiber30ParentOf 21 == 17
      && tttLargeFiber30ParentOf 17 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block6Chunk1Sources 6 0 == 1782
      && tttLargeFiber30ParentOf 1782 == 150
      && tttLargeFiber30ParentOf 150 == 22
      && tttLargeFiber30ParentOf 22 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block6Chunk1Sources 7 0 == 1783
      && tttLargeFiber30ParentOf 1783 == 151
      && tttLargeFiber30ParentOf 151 == 23
      && tttLargeFiber30ParentOf 23 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block6Chunk1Sources 8 0 == 1784
      && tttLargeFiber30ParentOf 1784 == 152
      && tttLargeFiber30ParentOf 152 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block6Chunk1Sources 9 0 == 1785
      && tttLargeFiber30ParentOf 1785 == 153
      && tttLargeFiber30ParentOf 153 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block6Chunk1Sources 10 0 == 1786
      && tttLargeFiber30ParentOf 1786 == 154
      && tttLargeFiber30ParentOf 154 == 26
      && tttLargeFiber30ParentOf 26 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block6Chunk1Sources 11 0 == 1787
      && tttLargeFiber30ParentOf 1787 == 155
      && tttLargeFiber30ParentOf 155 == 27
      && tttLargeFiber30ParentOf 27 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block6Chunk1Sources 12 0 == 1788
      && tttLargeFiber30ParentOf 1788 == 156
      && tttLargeFiber30ParentOf 156 == 28
      && tttLargeFiber30ParentOf 28 == 24
      && tttLargeFiber30ParentOf 24 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block6Chunk1Sources 13 0 == 1789
      && tttLargeFiber30ParentOf 1789 == 157
      && tttLargeFiber30ParentOf 157 == 29
      && tttLargeFiber30ParentOf 29 == 25
      && tttLargeFiber30ParentOf 25 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block6Chunk1Sources 14 0 == 1790
      && tttLargeFiber30ParentOf 1790 == 158
      && tttLargeFiber30ParentOf 158 == 30
      && tttLargeFiber30ParentOf 30 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block6Chunk1Sources 15 0 == 1791
      && tttLargeFiber30ParentOf 1791 == 159
      && tttLargeFiber30ParentOf 159 == 31
      && tttLargeFiber30ParentOf 31 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block6Chunk1Row_0_ok :
    tttLargeFiber30Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_1_ok :
    tttLargeFiber30Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_2_ok :
    tttLargeFiber30Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_3_ok :
    tttLargeFiber30Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_4_ok :
    tttLargeFiber30Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_5_ok :
    tttLargeFiber30Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_6_ok :
    tttLargeFiber30Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_7_ok :
    tttLargeFiber30Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_8_ok :
    tttLargeFiber30Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_9_ok :
    tttLargeFiber30Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_10_ok :
    tttLargeFiber30Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_11_ok :
    tttLargeFiber30Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_12_ok :
    tttLargeFiber30Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_13_ok :
    tttLargeFiber30Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_14_ok :
    tttLargeFiber30Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1Row_15_ok :
    tttLargeFiber30Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_0_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_1_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_2_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_3_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_4_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_5_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_6_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_7_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_8_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_9_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_10_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_11_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_12_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_13_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_14_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentMap_15_ok :
    tttLargeFiber30Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_0_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_1_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_2_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_3_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_4_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_5_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_6_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_7_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_8_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_9_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_10_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_11_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_12_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_13_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_14_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block6Chunk1ParentPath_15_ok :
    tttLargeFiber30Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber30Block6Chunk1RowCheck 0
    && tttLargeFiber30Block6Chunk1RowCheck 1
    && tttLargeFiber30Block6Chunk1RowCheck 2
    && tttLargeFiber30Block6Chunk1RowCheck 3
    && tttLargeFiber30Block6Chunk1RowCheck 4
    && tttLargeFiber30Block6Chunk1RowCheck 5
    && tttLargeFiber30Block6Chunk1RowCheck 6
    && tttLargeFiber30Block6Chunk1RowCheck 7
    && tttLargeFiber30Block6Chunk1RowCheck 8
    && tttLargeFiber30Block6Chunk1RowCheck 9
    && tttLargeFiber30Block6Chunk1RowCheck 10
    && tttLargeFiber30Block6Chunk1RowCheck 11
    && tttLargeFiber30Block6Chunk1RowCheck 12
    && tttLargeFiber30Block6Chunk1RowCheck 13
    && tttLargeFiber30Block6Chunk1RowCheck 14
    && tttLargeFiber30Block6Chunk1RowCheck 15

theorem tttLargeFiber30Block6Chunk1RowsAudit_ok :
    tttLargeFiber30Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber30Block6Chunk1RowsAudit,
    tttLargeFiber30Block6Chunk1Row_0_ok,
    tttLargeFiber30Block6Chunk1Row_1_ok,
    tttLargeFiber30Block6Chunk1Row_2_ok,
    tttLargeFiber30Block6Chunk1Row_3_ok,
    tttLargeFiber30Block6Chunk1Row_4_ok,
    tttLargeFiber30Block6Chunk1Row_5_ok,
    tttLargeFiber30Block6Chunk1Row_6_ok,
    tttLargeFiber30Block6Chunk1Row_7_ok,
    tttLargeFiber30Block6Chunk1Row_8_ok,
    tttLargeFiber30Block6Chunk1Row_9_ok,
    tttLargeFiber30Block6Chunk1Row_10_ok,
    tttLargeFiber30Block6Chunk1Row_11_ok,
    tttLargeFiber30Block6Chunk1Row_12_ok,
    tttLargeFiber30Block6Chunk1Row_13_ok,
    tttLargeFiber30Block6Chunk1Row_14_ok,
    tttLargeFiber30Block6Chunk1Row_15_ok]

def tttLargeFiber30Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber30Block6Chunk1ParentMapCheck 0
    && tttLargeFiber30Block6Chunk1ParentMapCheck 1
    && tttLargeFiber30Block6Chunk1ParentMapCheck 2
    && tttLargeFiber30Block6Chunk1ParentMapCheck 3
    && tttLargeFiber30Block6Chunk1ParentMapCheck 4
    && tttLargeFiber30Block6Chunk1ParentMapCheck 5
    && tttLargeFiber30Block6Chunk1ParentMapCheck 6
    && tttLargeFiber30Block6Chunk1ParentMapCheck 7
    && tttLargeFiber30Block6Chunk1ParentMapCheck 8
    && tttLargeFiber30Block6Chunk1ParentMapCheck 9
    && tttLargeFiber30Block6Chunk1ParentMapCheck 10
    && tttLargeFiber30Block6Chunk1ParentMapCheck 11
    && tttLargeFiber30Block6Chunk1ParentMapCheck 12
    && tttLargeFiber30Block6Chunk1ParentMapCheck 13
    && tttLargeFiber30Block6Chunk1ParentMapCheck 14
    && tttLargeFiber30Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber30Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber30Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber30Block6Chunk1ParentMapAudit,
    tttLargeFiber30Block6Chunk1ParentMap_0_ok,
    tttLargeFiber30Block6Chunk1ParentMap_1_ok,
    tttLargeFiber30Block6Chunk1ParentMap_2_ok,
    tttLargeFiber30Block6Chunk1ParentMap_3_ok,
    tttLargeFiber30Block6Chunk1ParentMap_4_ok,
    tttLargeFiber30Block6Chunk1ParentMap_5_ok,
    tttLargeFiber30Block6Chunk1ParentMap_6_ok,
    tttLargeFiber30Block6Chunk1ParentMap_7_ok,
    tttLargeFiber30Block6Chunk1ParentMap_8_ok,
    tttLargeFiber30Block6Chunk1ParentMap_9_ok,
    tttLargeFiber30Block6Chunk1ParentMap_10_ok,
    tttLargeFiber30Block6Chunk1ParentMap_11_ok,
    tttLargeFiber30Block6Chunk1ParentMap_12_ok,
    tttLargeFiber30Block6Chunk1ParentMap_13_ok,
    tttLargeFiber30Block6Chunk1ParentMap_14_ok,
    tttLargeFiber30Block6Chunk1ParentMap_15_ok]

def tttLargeFiber30Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber30Block6Chunk1ParentPathCheck 0
    && tttLargeFiber30Block6Chunk1ParentPathCheck 1
    && tttLargeFiber30Block6Chunk1ParentPathCheck 2
    && tttLargeFiber30Block6Chunk1ParentPathCheck 3
    && tttLargeFiber30Block6Chunk1ParentPathCheck 4
    && tttLargeFiber30Block6Chunk1ParentPathCheck 5
    && tttLargeFiber30Block6Chunk1ParentPathCheck 6
    && tttLargeFiber30Block6Chunk1ParentPathCheck 7
    && tttLargeFiber30Block6Chunk1ParentPathCheck 8
    && tttLargeFiber30Block6Chunk1ParentPathCheck 9
    && tttLargeFiber30Block6Chunk1ParentPathCheck 10
    && tttLargeFiber30Block6Chunk1ParentPathCheck 11
    && tttLargeFiber30Block6Chunk1ParentPathCheck 12
    && tttLargeFiber30Block6Chunk1ParentPathCheck 13
    && tttLargeFiber30Block6Chunk1ParentPathCheck 14
    && tttLargeFiber30Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber30Block6Chunk1ParentsAudit_ok :
    tttLargeFiber30Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber30Block6Chunk1ParentsAudit,
    tttLargeFiber30Block6Chunk1ParentPath_0_ok,
    tttLargeFiber30Block6Chunk1ParentPath_1_ok,
    tttLargeFiber30Block6Chunk1ParentPath_2_ok,
    tttLargeFiber30Block6Chunk1ParentPath_3_ok,
    tttLargeFiber30Block6Chunk1ParentPath_4_ok,
    tttLargeFiber30Block6Chunk1ParentPath_5_ok,
    tttLargeFiber30Block6Chunk1ParentPath_6_ok,
    tttLargeFiber30Block6Chunk1ParentPath_7_ok,
    tttLargeFiber30Block6Chunk1ParentPath_8_ok,
    tttLargeFiber30Block6Chunk1ParentPath_9_ok,
    tttLargeFiber30Block6Chunk1ParentPath_10_ok,
    tttLargeFiber30Block6Chunk1ParentPath_11_ok,
    tttLargeFiber30Block6Chunk1ParentPath_12_ok,
    tttLargeFiber30Block6Chunk1ParentPath_13_ok,
    tttLargeFiber30Block6Chunk1ParentPath_14_ok,
    tttLargeFiber30Block6Chunk1ParentPath_15_ok]

def tttLargeFiber30Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block6Chunk1SourcesCheck &&
    tttLargeFiber30Block6Chunk1RowsAudit &&
    tttLargeFiber30Block6Chunk1ParentMapAudit &&
    tttLargeFiber30Block6Chunk1ParentsAudit

theorem tttLargeFiber30Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber30Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block6Chunk1SourcesCheck_ok,
    tttLargeFiber30Block6Chunk1RowsAudit_ok,
    tttLargeFiber30Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber30Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
