import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleLightSlices
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk0ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first `MMM` large-fiber chunk

This module starts the large-fiber part of the `MMM`/`mode05` representative
target.  It reuses one existing 16-row `TTT` large-fiber chunk and rechecks it
against the actual mirror-triple word and the reversed fixed-input key
`[b,b,r,r]`.

This is one large fixed-input chunk, not the full `MMM` target audit and not
the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLargeFiber36Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818MirrorTripleComponentSmoke
open GoertzelLemma818MirrorTripleLightSlices
open GoertzelLemma818TripleTauLargeFiber4Data
open GoertzelLemma818TripleTauLargeFiber4Block1Chunk0ComponentCertificate

def mmmLargeFiber36Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.r]

def mmmLargeFiber36Expected : List Nat :=
  tttLargeFiber4Expected

def mmmLargeFiber36Block1Chunk0Sources : List Nat :=
  tttLargeFiber4Block1Chunk0Sources

def mmmLargeFiber36Block1Chunk0Rows :=
  tttLargeFiber4Block1Chunk0Rows

def mmmLargeFiber36Block1Chunk0SourcesCheck : Bool :=
  (mmmLargeFiber36Block1Chunk0Rows.map fun row => row.source) ==
    mmmLargeFiber36Block1Chunk0Sources

theorem mmmLargeFiber36Block1Chunk0SourcesCheck_ok :
    mmmLargeFiber36Block1Chunk0SourcesCheck = true := by
  decide

def mmmLargeFiber36Block1Chunk0RowCheck (i : Nat) : Bool :=
  mmmLightComponentRowValid mmmLargeFiber36Key mmmLargeFiber36Expected
    (listGetD mmmLargeFiber36Block1Chunk0Rows i default)

def mmmLargeFiber36Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD mmmLargeFiber36Block1Chunk0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def mmmLargeFiber36Block1Chunk0ParentConvergesCheck (i : Nat) : Bool :=
  tttLargeFiber4ParentIter tttLargeFiber4MaxParentDepth
    (listGetD mmmLargeFiber36Block1Chunk0Sources i 0) ==
      tttLargeFiber4Root

theorem mmmLargeFiber36Block1Chunk0Row_0_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 0 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_1_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 1 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_2_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 2 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_3_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 3 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_4_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 4 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_5_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 5 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_6_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 6 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_7_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 7 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_8_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 8 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_9_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 9 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_10_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 10 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_11_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 11 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_12_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 12 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_13_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 13 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_14_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 14 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Row_15_ok :
    mmmLargeFiber36Block1Chunk0RowCheck 15 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_0_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_1_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_2_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_3_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_4_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_5_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_6_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_7_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_8_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_9_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_10_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_11_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_12_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_13_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_14_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0ParentMap_15_ok :
    mmmLargeFiber36Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_0_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 0 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_1_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 1 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_2_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 2 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_3_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 3 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_4_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 4 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_5_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 5 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_6_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 6 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_7_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 7 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_8_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 8 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_9_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 9 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_10_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 10 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_11_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 11 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_12_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 12 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_13_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 13 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_14_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 14 = true := by
  decide

theorem mmmLargeFiber36Block1Chunk0Parent_15_ok :
    mmmLargeFiber36Block1Chunk0ParentConvergesCheck 15 = true := by
  decide

def mmmLargeFiber36Block1Chunk0RowsAudit : Bool :=
  mmmLargeFiber36Block1Chunk0RowCheck 0
    && mmmLargeFiber36Block1Chunk0RowCheck 1
    && mmmLargeFiber36Block1Chunk0RowCheck 2
    && mmmLargeFiber36Block1Chunk0RowCheck 3
    && mmmLargeFiber36Block1Chunk0RowCheck 4
    && mmmLargeFiber36Block1Chunk0RowCheck 5
    && mmmLargeFiber36Block1Chunk0RowCheck 6
    && mmmLargeFiber36Block1Chunk0RowCheck 7
    && mmmLargeFiber36Block1Chunk0RowCheck 8
    && mmmLargeFiber36Block1Chunk0RowCheck 9
    && mmmLargeFiber36Block1Chunk0RowCheck 10
    && mmmLargeFiber36Block1Chunk0RowCheck 11
    && mmmLargeFiber36Block1Chunk0RowCheck 12
    && mmmLargeFiber36Block1Chunk0RowCheck 13
    && mmmLargeFiber36Block1Chunk0RowCheck 14
    && mmmLargeFiber36Block1Chunk0RowCheck 15

theorem mmmLargeFiber36Block1Chunk0RowsAudit_ok :
    mmmLargeFiber36Block1Chunk0RowsAudit = true := by
  simp [mmmLargeFiber36Block1Chunk0RowsAudit,
    mmmLargeFiber36Block1Chunk0Row_0_ok,
    mmmLargeFiber36Block1Chunk0Row_1_ok,
    mmmLargeFiber36Block1Chunk0Row_2_ok,
    mmmLargeFiber36Block1Chunk0Row_3_ok,
    mmmLargeFiber36Block1Chunk0Row_4_ok,
    mmmLargeFiber36Block1Chunk0Row_5_ok,
    mmmLargeFiber36Block1Chunk0Row_6_ok,
    mmmLargeFiber36Block1Chunk0Row_7_ok,
    mmmLargeFiber36Block1Chunk0Row_8_ok,
    mmmLargeFiber36Block1Chunk0Row_9_ok,
    mmmLargeFiber36Block1Chunk0Row_10_ok,
    mmmLargeFiber36Block1Chunk0Row_11_ok,
    mmmLargeFiber36Block1Chunk0Row_12_ok,
    mmmLargeFiber36Block1Chunk0Row_13_ok,
    mmmLargeFiber36Block1Chunk0Row_14_ok,
    mmmLargeFiber36Block1Chunk0Row_15_ok]

def mmmLargeFiber36Block1Chunk0ParentMapAudit : Bool :=
  mmmLargeFiber36Block1Chunk0ParentMapCheck 0
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 1
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 2
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 3
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 4
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 5
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 6
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 7
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 8
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 9
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 10
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 11
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 12
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 13
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 14
    && mmmLargeFiber36Block1Chunk0ParentMapCheck 15

theorem mmmLargeFiber36Block1Chunk0ParentMapAudit_ok :
    mmmLargeFiber36Block1Chunk0ParentMapAudit = true := by
  simp [mmmLargeFiber36Block1Chunk0ParentMapAudit,
    mmmLargeFiber36Block1Chunk0ParentMap_0_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_1_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_2_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_3_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_4_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_5_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_6_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_7_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_8_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_9_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_10_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_11_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_12_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_13_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_14_ok,
    mmmLargeFiber36Block1Chunk0ParentMap_15_ok]

def mmmLargeFiber36Block1Chunk0ParentsAudit : Bool :=
  mmmLargeFiber36Block1Chunk0ParentConvergesCheck 0
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 1
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 2
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 3
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 4
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 5
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 6
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 7
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 8
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 9
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 10
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 11
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 12
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 13
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 14
    && mmmLargeFiber36Block1Chunk0ParentConvergesCheck 15

theorem mmmLargeFiber36Block1Chunk0ParentsAudit_ok :
    mmmLargeFiber36Block1Chunk0ParentsAudit = true := by
  simp [mmmLargeFiber36Block1Chunk0ParentsAudit,
    mmmLargeFiber36Block1Chunk0Parent_0_ok,
    mmmLargeFiber36Block1Chunk0Parent_1_ok,
    mmmLargeFiber36Block1Chunk0Parent_2_ok,
    mmmLargeFiber36Block1Chunk0Parent_3_ok,
    mmmLargeFiber36Block1Chunk0Parent_4_ok,
    mmmLargeFiber36Block1Chunk0Parent_5_ok,
    mmmLargeFiber36Block1Chunk0Parent_6_ok,
    mmmLargeFiber36Block1Chunk0Parent_7_ok,
    mmmLargeFiber36Block1Chunk0Parent_8_ok,
    mmmLargeFiber36Block1Chunk0Parent_9_ok,
    mmmLargeFiber36Block1Chunk0Parent_10_ok,
    mmmLargeFiber36Block1Chunk0Parent_11_ok,
    mmmLargeFiber36Block1Chunk0Parent_12_ok,
    mmmLargeFiber36Block1Chunk0Parent_13_ok,
    mmmLargeFiber36Block1Chunk0Parent_14_ok,
    mmmLargeFiber36Block1Chunk0Parent_15_ok]

def mmmLargeFiber36Block1Chunk0ComponentCertificateAudit : Bool :=
  mmmRepresentativeModeSliceAudit &&
    tttLargeFiber4CountsAudit &&
    mmmLargeFiber36Block1Chunk0SourcesCheck &&
    mmmLargeFiber36Block1Chunk0RowsAudit &&
    mmmLargeFiber36Block1Chunk0ParentMapAudit &&
    mmmLargeFiber36Block1Chunk0ParentsAudit

theorem mmmLargeFiber36Block1Chunk0ComponentCertificateAudit_ok :
    mmmLargeFiber36Block1Chunk0ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block1Chunk0ComponentCertificateAudit,
    mmmRepresentativeModeSliceAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    mmmLargeFiber36Block1Chunk0SourcesCheck_ok,
    mmmLargeFiber36Block1Chunk0RowsAudit_ok,
    mmmLargeFiber36Block1Chunk0ParentMapAudit_ok,
    mmmLargeFiber36Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818MirrorTripleLargeFiber36Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
