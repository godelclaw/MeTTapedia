import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleComponentSmoke
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLightComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: `MMM` light-fiber slices

This module starts scaling the `MMM`/`mode05` representative certificate beyond
the initial smoke fiber.  It reuses an existing `TTT` light-fiber row set and
rechecks it against the actual mirror-chain word and reversed outer input key.

It is still a partial light-fiber certificate for `MMM`, not a full `MMM`
target audit and not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLightSlices

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818MirrorTripleComponentSmoke

def mmmLightComponentRowValid
    (key : List LColor) (expected : List Nat)
    (row :
      GoertzelLemma818TripleTauLightComponentCertificate.TripleComponentParentRow) :
    Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := GoertzelLemma818TripleTauLightComponentCertificate.tripleStates
      row.sourceLeft row.sourceMiddle row.sourceRight
    let t := GoertzelLemma818TripleTauLightComponentCertificate.tripleStates
      row.parentLeft row.parentMiddle row.parentRight
    compatibleChainStates mmmWord s && compatibleChainStates mmmWord t &&
      chainInputKey mmmWord s == key && chainInputKey mmmWord t == key &&
        (row.source == row.parent ||
          chainCertifiedKempeStep mmmWord s t row.cert)

def mmmFiber63Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.r]

def mmmFiber63Expected : List Nat :=
  GoertzelLemma818TripleTauLightComponentCertificate.tttFiber5Expected

def mmmFiber63Rows :
    List GoertzelLemma818TripleTauLightComponentCertificate.TripleComponentParentRow :=
  GoertzelLemma818TripleTauLightComponentCertificate.tttFiber5Rows

def mmmFiber63SourcesCheck : Bool :=
  (mmmFiber63Rows.map fun row => row.source) == mmmFiber63Expected

theorem mmmFiber63SourcesCheck_ok :
    mmmFiber63SourcesCheck = true := by
  decide

def mmmFiber63RowCheck (i : Nat) : Bool :=
  mmmLightComponentRowValid mmmFiber63Key mmmFiber63Expected
    (listGetD mmmFiber63Rows i default)

theorem mmmFiber63Row_0_ok : mmmFiber63RowCheck 0 = true := by decide
theorem mmmFiber63Row_1_ok : mmmFiber63RowCheck 1 = true := by decide
theorem mmmFiber63Row_2_ok : mmmFiber63RowCheck 2 = true := by decide
theorem mmmFiber63Row_3_ok : mmmFiber63RowCheck 3 = true := by decide
theorem mmmFiber63Row_4_ok : mmmFiber63RowCheck 4 = true := by decide
theorem mmmFiber63Row_5_ok : mmmFiber63RowCheck 5 = true := by decide
theorem mmmFiber63Row_6_ok : mmmFiber63RowCheck 6 = true := by decide
theorem mmmFiber63Row_7_ok : mmmFiber63RowCheck 7 = true := by decide
theorem mmmFiber63Row_8_ok : mmmFiber63RowCheck 8 = true := by decide
theorem mmmFiber63Row_9_ok : mmmFiber63RowCheck 9 = true := by decide
theorem mmmFiber63Row_10_ok : mmmFiber63RowCheck 10 = true := by decide
theorem mmmFiber63Row_11_ok : mmmFiber63RowCheck 11 = true := by decide
theorem mmmFiber63Row_12_ok : mmmFiber63RowCheck 12 = true := by decide
theorem mmmFiber63Row_13_ok : mmmFiber63RowCheck 13 = true := by decide
theorem mmmFiber63Row_14_ok : mmmFiber63RowCheck 14 = true := by decide
theorem mmmFiber63Row_15_ok : mmmFiber63RowCheck 15 = true := by decide

def mmmFiber63ParentCheck (i : Nat) : Bool :=
  GoertzelLemma818TripleTauLightComponentCertificate.tripleParentIter
    mmmFiber63Rows
    GoertzelLemma818TripleTauLightComponentCertificate.tttLightMaxParentDepth
    (listGetD mmmFiber63Expected i 0) == 2432

theorem mmmFiber63Parent_0_ok : mmmFiber63ParentCheck 0 = true := by decide
theorem mmmFiber63Parent_1_ok : mmmFiber63ParentCheck 1 = true := by decide
theorem mmmFiber63Parent_2_ok : mmmFiber63ParentCheck 2 = true := by decide
theorem mmmFiber63Parent_3_ok : mmmFiber63ParentCheck 3 = true := by decide
theorem mmmFiber63Parent_4_ok : mmmFiber63ParentCheck 4 = true := by decide
theorem mmmFiber63Parent_5_ok : mmmFiber63ParentCheck 5 = true := by decide
theorem mmmFiber63Parent_6_ok : mmmFiber63ParentCheck 6 = true := by decide
theorem mmmFiber63Parent_7_ok : mmmFiber63ParentCheck 7 = true := by decide
theorem mmmFiber63Parent_8_ok : mmmFiber63ParentCheck 8 = true := by decide
theorem mmmFiber63Parent_9_ok : mmmFiber63ParentCheck 9 = true := by decide
theorem mmmFiber63Parent_10_ok : mmmFiber63ParentCheck 10 = true := by decide
theorem mmmFiber63Parent_11_ok : mmmFiber63ParentCheck 11 = true := by decide
theorem mmmFiber63Parent_12_ok : mmmFiber63ParentCheck 12 = true := by decide
theorem mmmFiber63Parent_13_ok : mmmFiber63ParentCheck 13 = true := by decide
theorem mmmFiber63Parent_14_ok : mmmFiber63ParentCheck 14 = true := by decide
theorem mmmFiber63Parent_15_ok : mmmFiber63ParentCheck 15 = true := by decide

def mmmFiber63ComponentCertificateAudit : Bool :=
  mmmRepresentativeModeSliceAudit &&
    mmmFiber63SourcesCheck &&
    mmmFiber63RowCheck 0 &&
    mmmFiber63RowCheck 1 &&
    mmmFiber63RowCheck 2 &&
    mmmFiber63RowCheck 3 &&
    mmmFiber63RowCheck 4 &&
    mmmFiber63RowCheck 5 &&
    mmmFiber63RowCheck 6 &&
    mmmFiber63RowCheck 7 &&
    mmmFiber63RowCheck 8 &&
    mmmFiber63RowCheck 9 &&
    mmmFiber63RowCheck 10 &&
    mmmFiber63RowCheck 11 &&
    mmmFiber63RowCheck 12 &&
    mmmFiber63RowCheck 13 &&
    mmmFiber63RowCheck 14 &&
    mmmFiber63RowCheck 15 &&
    mmmFiber63ParentCheck 0 &&
    mmmFiber63ParentCheck 1 &&
    mmmFiber63ParentCheck 2 &&
    mmmFiber63ParentCheck 3 &&
    mmmFiber63ParentCheck 4 &&
    mmmFiber63ParentCheck 5 &&
    mmmFiber63ParentCheck 6 &&
    mmmFiber63ParentCheck 7 &&
    mmmFiber63ParentCheck 8 &&
    mmmFiber63ParentCheck 9 &&
    mmmFiber63ParentCheck 10 &&
    mmmFiber63ParentCheck 11 &&
    mmmFiber63ParentCheck 12 &&
    mmmFiber63ParentCheck 13 &&
    mmmFiber63ParentCheck 14 &&
    mmmFiber63ParentCheck 15

theorem mmmFiber63ComponentCertificateAudit_ok :
    mmmFiber63ComponentCertificateAudit = true := by
  simp [mmmFiber63ComponentCertificateAudit,
    mmmRepresentativeModeSliceAudit_ok,
    mmmFiber63SourcesCheck_ok,
    mmmFiber63Row_0_ok,
    mmmFiber63Row_1_ok,
    mmmFiber63Row_2_ok,
    mmmFiber63Row_3_ok,
    mmmFiber63Row_4_ok,
    mmmFiber63Row_5_ok,
    mmmFiber63Row_6_ok,
    mmmFiber63Row_7_ok,
    mmmFiber63Row_8_ok,
    mmmFiber63Row_9_ok,
    mmmFiber63Row_10_ok,
    mmmFiber63Row_11_ok,
    mmmFiber63Row_12_ok,
    mmmFiber63Row_13_ok,
    mmmFiber63Row_14_ok,
    mmmFiber63Row_15_ok,
    mmmFiber63Parent_0_ok,
    mmmFiber63Parent_1_ok,
    mmmFiber63Parent_2_ok,
    mmmFiber63Parent_3_ok,
    mmmFiber63Parent_4_ok,
    mmmFiber63Parent_5_ok,
    mmmFiber63Parent_6_ok,
    mmmFiber63Parent_7_ok,
    mmmFiber63Parent_8_ok,
    mmmFiber63Parent_9_ok,
    mmmFiber63Parent_10_ok,
    mmmFiber63Parent_11_ok,
    mmmFiber63Parent_12_ok,
    mmmFiber63Parent_13_ok,
    mmmFiber63Parent_14_ok,
    mmmFiber63Parent_15_ok]

def mmmCheckedLightSliceCountAfterFiber63 : Nat := 2

def mmmCheckedLightSlicesAfterFiber63Audit : Bool :=
  mmmFiber9ComponentCertificateAudit &&
    mmmFiber63ComponentCertificateAudit &&
    mmmCheckedLightSliceCountAfterFiber63 == 2

theorem mmmCheckedLightSlicesAfterFiber63Audit_ok :
    mmmCheckedLightSlicesAfterFiber63Audit = true := by
  simp [mmmCheckedLightSlicesAfterFiber63Audit,
    mmmCheckedLightSliceCountAfterFiber63,
    mmmFiber9ComponentCertificateAudit_ok,
    mmmFiber63ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLightSlices

end Mettapedia.GraphTheory.FourColor
