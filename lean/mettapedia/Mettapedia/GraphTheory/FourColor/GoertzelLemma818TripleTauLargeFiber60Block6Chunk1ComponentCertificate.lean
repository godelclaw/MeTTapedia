import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 6 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block6Chunk1Sources : List Nat :=
  [   1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239,
   1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]

def tttLargeFiber60Row400 : TripleComponentParentRow :=
  tripleRow 1232 688 34 2 16 18 18 16
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row401 : TripleComponentParentRow :=
  tripleRow 1233 689 34 2 17 18 18 17
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row402 : TripleComponentParentRow :=
  tripleRow 1234 690 34 2 18 18 18 18
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row403 : TripleComponentParentRow :=
  tripleRow 1235 691 34 2 19 18 18 19
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row404 : TripleComponentParentRow :=
  tripleRow 1236 692 34 2 32 18 18 32
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row405 : TripleComponentParentRow :=
  tripleRow 1237 693 34 2 33 18 18 33
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row406 : TripleComponentParentRow :=
  tripleRow 1238 694 34 2 34 18 18 34
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row407 : TripleComponentParentRow :=
  tripleRow 1239 695 34 2 35 18 18 35
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row408 : TripleComponentParentRow :=
  tripleRow 1240 696 34 3 24 18 19 24
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row409 : TripleComponentParentRow :=
  tripleRow 1241 697 34 3 25 18 19 25
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row410 : TripleComponentParentRow :=
  tripleRow 1242 698 34 3 26 18 19 26
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row411 : TripleComponentParentRow :=
  tripleRow 1243 699 34 3 27 18 19 27
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row412 : TripleComponentParentRow :=
  tripleRow 1244 700 34 3 40 18 19 40
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row413 : TripleComponentParentRow :=
  tripleRow 1245 701 34 3 41 18 19 41
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row414 : TripleComponentParentRow :=
  tripleRow 1246 702 34 3 42 18 19 42
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row415 : TripleComponentParentRow :=
  tripleRow 1247 703 34 3 43 18 19 43
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row400
  , tttLargeFiber60Row401
  , tttLargeFiber60Row402
  , tttLargeFiber60Row403
  , tttLargeFiber60Row404
  , tttLargeFiber60Row405
  , tttLargeFiber60Row406
  , tttLargeFiber60Row407
  , tttLargeFiber60Row408
  , tttLargeFiber60Row409
  , tttLargeFiber60Row410
  , tttLargeFiber60Row411
  , tttLargeFiber60Row412
  , tttLargeFiber60Row413
  , tttLargeFiber60Row414
  , tttLargeFiber60Row415
  ]

def tttLargeFiber60Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber60Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber60Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber60Block6Chunk1Sources

theorem tttLargeFiber60Block6Chunk1SourcesCheck_ok :
    tttLargeFiber60Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber60Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block6Chunk1RowValid
    (listGetD tttLargeFiber60Block6Chunk1Rows i default)

def tttLargeFiber60Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block6Chunk1Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block6Chunk1Sources 0 0 == 1232
      && tttLargeFiber60ParentOf 1232 == 688
      && tttLargeFiber60ParentOf 688 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block6Chunk1Sources 1 0 == 1233
      && tttLargeFiber60ParentOf 1233 == 689
      && tttLargeFiber60ParentOf 689 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block6Chunk1Sources 2 0 == 1234
      && tttLargeFiber60ParentOf 1234 == 690
      && tttLargeFiber60ParentOf 690 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block6Chunk1Sources 3 0 == 1235
      && tttLargeFiber60ParentOf 1235 == 691
      && tttLargeFiber60ParentOf 691 == 563
      && tttLargeFiber60ParentOf 563 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block6Chunk1Sources 4 0 == 1236
      && tttLargeFiber60ParentOf 1236 == 692
      && tttLargeFiber60ParentOf 692 == 564
      && tttLargeFiber60ParentOf 564 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block6Chunk1Sources 5 0 == 1237
      && tttLargeFiber60ParentOf 1237 == 693
      && tttLargeFiber60ParentOf 693 == 565
      && tttLargeFiber60ParentOf 565 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block6Chunk1Sources 6 0 == 1238
      && tttLargeFiber60ParentOf 1238 == 694
      && tttLargeFiber60ParentOf 694 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block6Chunk1Sources 7 0 == 1239
      && tttLargeFiber60ParentOf 1239 == 695
      && tttLargeFiber60ParentOf 695 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block6Chunk1Sources 8 0 == 1240
      && tttLargeFiber60ParentOf 1240 == 696
      && tttLargeFiber60ParentOf 696 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block6Chunk1Sources 9 0 == 1241
      && tttLargeFiber60ParentOf 1241 == 697
      && tttLargeFiber60ParentOf 697 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block6Chunk1Sources 10 0 == 1242
      && tttLargeFiber60ParentOf 1242 == 698
      && tttLargeFiber60ParentOf 698 == 570
      && tttLargeFiber60ParentOf 570 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block6Chunk1Sources 11 0 == 1243
      && tttLargeFiber60ParentOf 1243 == 699
      && tttLargeFiber60ParentOf 699 == 571
      && tttLargeFiber60ParentOf 571 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block6Chunk1Sources 12 0 == 1244
      && tttLargeFiber60ParentOf 1244 == 700
      && tttLargeFiber60ParentOf 700 == 572
      && tttLargeFiber60ParentOf 572 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block6Chunk1Sources 13 0 == 1245
      && tttLargeFiber60ParentOf 1245 == 701
      && tttLargeFiber60ParentOf 701 == 573
      && tttLargeFiber60ParentOf 573 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block6Chunk1Sources 14 0 == 1246
      && tttLargeFiber60ParentOf 1246 == 702
      && tttLargeFiber60ParentOf 702 == 574
      && tttLargeFiber60ParentOf 574 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block6Chunk1Sources 15 0 == 1247
      && tttLargeFiber60ParentOf 1247 == 703
      && tttLargeFiber60ParentOf 703 == 575
      && tttLargeFiber60ParentOf 575 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block6Chunk1Row_0_ok :
    tttLargeFiber60Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_1_ok :
    tttLargeFiber60Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_2_ok :
    tttLargeFiber60Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_3_ok :
    tttLargeFiber60Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_4_ok :
    tttLargeFiber60Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_5_ok :
    tttLargeFiber60Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_6_ok :
    tttLargeFiber60Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_7_ok :
    tttLargeFiber60Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_8_ok :
    tttLargeFiber60Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_9_ok :
    tttLargeFiber60Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_10_ok :
    tttLargeFiber60Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_11_ok :
    tttLargeFiber60Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_12_ok :
    tttLargeFiber60Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_13_ok :
    tttLargeFiber60Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_14_ok :
    tttLargeFiber60Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1Row_15_ok :
    tttLargeFiber60Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_0_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_1_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_2_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_3_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_4_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_5_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_6_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_7_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_8_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_9_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_10_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_11_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_12_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_13_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_14_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentMap_15_ok :
    tttLargeFiber60Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_0_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_1_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_2_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_3_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_4_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_5_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_6_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_7_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_8_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_9_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_10_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_11_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_12_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_13_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_14_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block6Chunk1ParentPath_15_ok :
    tttLargeFiber60Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber60Block6Chunk1RowCheck 0
    && tttLargeFiber60Block6Chunk1RowCheck 1
    && tttLargeFiber60Block6Chunk1RowCheck 2
    && tttLargeFiber60Block6Chunk1RowCheck 3
    && tttLargeFiber60Block6Chunk1RowCheck 4
    && tttLargeFiber60Block6Chunk1RowCheck 5
    && tttLargeFiber60Block6Chunk1RowCheck 6
    && tttLargeFiber60Block6Chunk1RowCheck 7
    && tttLargeFiber60Block6Chunk1RowCheck 8
    && tttLargeFiber60Block6Chunk1RowCheck 9
    && tttLargeFiber60Block6Chunk1RowCheck 10
    && tttLargeFiber60Block6Chunk1RowCheck 11
    && tttLargeFiber60Block6Chunk1RowCheck 12
    && tttLargeFiber60Block6Chunk1RowCheck 13
    && tttLargeFiber60Block6Chunk1RowCheck 14
    && tttLargeFiber60Block6Chunk1RowCheck 15

theorem tttLargeFiber60Block6Chunk1RowsAudit_ok :
    tttLargeFiber60Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber60Block6Chunk1RowsAudit,
    tttLargeFiber60Block6Chunk1Row_0_ok,
    tttLargeFiber60Block6Chunk1Row_1_ok,
    tttLargeFiber60Block6Chunk1Row_2_ok,
    tttLargeFiber60Block6Chunk1Row_3_ok,
    tttLargeFiber60Block6Chunk1Row_4_ok,
    tttLargeFiber60Block6Chunk1Row_5_ok,
    tttLargeFiber60Block6Chunk1Row_6_ok,
    tttLargeFiber60Block6Chunk1Row_7_ok,
    tttLargeFiber60Block6Chunk1Row_8_ok,
    tttLargeFiber60Block6Chunk1Row_9_ok,
    tttLargeFiber60Block6Chunk1Row_10_ok,
    tttLargeFiber60Block6Chunk1Row_11_ok,
    tttLargeFiber60Block6Chunk1Row_12_ok,
    tttLargeFiber60Block6Chunk1Row_13_ok,
    tttLargeFiber60Block6Chunk1Row_14_ok,
    tttLargeFiber60Block6Chunk1Row_15_ok]

def tttLargeFiber60Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber60Block6Chunk1ParentMapCheck 0
    && tttLargeFiber60Block6Chunk1ParentMapCheck 1
    && tttLargeFiber60Block6Chunk1ParentMapCheck 2
    && tttLargeFiber60Block6Chunk1ParentMapCheck 3
    && tttLargeFiber60Block6Chunk1ParentMapCheck 4
    && tttLargeFiber60Block6Chunk1ParentMapCheck 5
    && tttLargeFiber60Block6Chunk1ParentMapCheck 6
    && tttLargeFiber60Block6Chunk1ParentMapCheck 7
    && tttLargeFiber60Block6Chunk1ParentMapCheck 8
    && tttLargeFiber60Block6Chunk1ParentMapCheck 9
    && tttLargeFiber60Block6Chunk1ParentMapCheck 10
    && tttLargeFiber60Block6Chunk1ParentMapCheck 11
    && tttLargeFiber60Block6Chunk1ParentMapCheck 12
    && tttLargeFiber60Block6Chunk1ParentMapCheck 13
    && tttLargeFiber60Block6Chunk1ParentMapCheck 14
    && tttLargeFiber60Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber60Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber60Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber60Block6Chunk1ParentMapAudit,
    tttLargeFiber60Block6Chunk1ParentMap_0_ok,
    tttLargeFiber60Block6Chunk1ParentMap_1_ok,
    tttLargeFiber60Block6Chunk1ParentMap_2_ok,
    tttLargeFiber60Block6Chunk1ParentMap_3_ok,
    tttLargeFiber60Block6Chunk1ParentMap_4_ok,
    tttLargeFiber60Block6Chunk1ParentMap_5_ok,
    tttLargeFiber60Block6Chunk1ParentMap_6_ok,
    tttLargeFiber60Block6Chunk1ParentMap_7_ok,
    tttLargeFiber60Block6Chunk1ParentMap_8_ok,
    tttLargeFiber60Block6Chunk1ParentMap_9_ok,
    tttLargeFiber60Block6Chunk1ParentMap_10_ok,
    tttLargeFiber60Block6Chunk1ParentMap_11_ok,
    tttLargeFiber60Block6Chunk1ParentMap_12_ok,
    tttLargeFiber60Block6Chunk1ParentMap_13_ok,
    tttLargeFiber60Block6Chunk1ParentMap_14_ok,
    tttLargeFiber60Block6Chunk1ParentMap_15_ok]

def tttLargeFiber60Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber60Block6Chunk1ParentPathCheck 0
    && tttLargeFiber60Block6Chunk1ParentPathCheck 1
    && tttLargeFiber60Block6Chunk1ParentPathCheck 2
    && tttLargeFiber60Block6Chunk1ParentPathCheck 3
    && tttLargeFiber60Block6Chunk1ParentPathCheck 4
    && tttLargeFiber60Block6Chunk1ParentPathCheck 5
    && tttLargeFiber60Block6Chunk1ParentPathCheck 6
    && tttLargeFiber60Block6Chunk1ParentPathCheck 7
    && tttLargeFiber60Block6Chunk1ParentPathCheck 8
    && tttLargeFiber60Block6Chunk1ParentPathCheck 9
    && tttLargeFiber60Block6Chunk1ParentPathCheck 10
    && tttLargeFiber60Block6Chunk1ParentPathCheck 11
    && tttLargeFiber60Block6Chunk1ParentPathCheck 12
    && tttLargeFiber60Block6Chunk1ParentPathCheck 13
    && tttLargeFiber60Block6Chunk1ParentPathCheck 14
    && tttLargeFiber60Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber60Block6Chunk1ParentsAudit_ok :
    tttLargeFiber60Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber60Block6Chunk1ParentsAudit,
    tttLargeFiber60Block6Chunk1ParentPath_0_ok,
    tttLargeFiber60Block6Chunk1ParentPath_1_ok,
    tttLargeFiber60Block6Chunk1ParentPath_2_ok,
    tttLargeFiber60Block6Chunk1ParentPath_3_ok,
    tttLargeFiber60Block6Chunk1ParentPath_4_ok,
    tttLargeFiber60Block6Chunk1ParentPath_5_ok,
    tttLargeFiber60Block6Chunk1ParentPath_6_ok,
    tttLargeFiber60Block6Chunk1ParentPath_7_ok,
    tttLargeFiber60Block6Chunk1ParentPath_8_ok,
    tttLargeFiber60Block6Chunk1ParentPath_9_ok,
    tttLargeFiber60Block6Chunk1ParentPath_10_ok,
    tttLargeFiber60Block6Chunk1ParentPath_11_ok,
    tttLargeFiber60Block6Chunk1ParentPath_12_ok,
    tttLargeFiber60Block6Chunk1ParentPath_13_ok,
    tttLargeFiber60Block6Chunk1ParentPath_14_ok,
    tttLargeFiber60Block6Chunk1ParentPath_15_ok]

def tttLargeFiber60Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block6Chunk1SourcesCheck &&
    tttLargeFiber60Block6Chunk1RowsAudit &&
    tttLargeFiber60Block6Chunk1ParentMapAudit &&
    tttLargeFiber60Block6Chunk1ParentsAudit

theorem tttLargeFiber60Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber60Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block6Chunk1SourcesCheck_ok,
    tttLargeFiber60Block6Chunk1RowsAudit_ok,
    tttLargeFiber60Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber60Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
