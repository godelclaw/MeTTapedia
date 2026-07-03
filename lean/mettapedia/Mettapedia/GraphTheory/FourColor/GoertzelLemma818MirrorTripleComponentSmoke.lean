import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauComponentSmoke

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: `MMM` representative component smoke check

This module checks one small fixed-input fiber of the non-base representative
word `mirror-tau,mirror-tau,mirror-tau`
(`RepresentativeSemanticTarget.mmm`, profile `mode05`).  It reuses the same
explicit parent rows as the corresponding `TTT` smoke slice, but rechecks every
row against the actual mirror-chain orientation word and the reversed outer
input key.

This is a row-split component-certificate slice for a second remaining
semantic target, not the full `MMM` target audit and not the all-chain
`LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleComponentSmoke

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate

def mmmWord : List TauOrient :=
  [TauOrient.mirror, TauOrient.mirror, TauOrient.mirror]

def mmmFrontierWord :
    List GoertzelLemma818FrontierMode.TauOrient :=
  [ GoertzelLemma818FrontierMode.TauOrient.mirror
  , GoertzelLemma818FrontierMode.TauOrient.mirror
  , GoertzelLemma818FrontierMode.TauOrient.mirror
  ]

def mmmRepresentativeModeSliceAudit : Bool :=
  GoertzelLemma818RepresentativeTargets.targetFrontierWord
      GoertzelLemma818RepresentativeTargets.RepresentativeSemanticTarget.mmm ==
    mmmFrontierWord
  && GoertzelLemma818RepresentativeTargets.targetFrontierMode
      GoertzelLemma818RepresentativeTargets.RepresentativeSemanticTarget.mmm ==
    GoertzelLemma818FrontierMode.FrontierMode.mode05
  && GoertzelLemma818FrontierMode.wordMode mmmFrontierWord ==
    some GoertzelLemma818FrontierMode.FrontierMode.mode05

theorem mmmRepresentativeModeSliceAudit_ok :
    mmmRepresentativeModeSliceAudit = true := by
  decide

def mmmFiber9Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.r]

def mmmFiber9Expected : List Nat :=
  GoertzelLemma818TripleTauComponentSmoke.tttFiber3Expected

def mmmFiber9Rows :
    List GoertzelLemma818TripleTauComponentSmoke.TripleComponentParentRow :=
  GoertzelLemma818TripleTauComponentSmoke.tttFiber3Rows

def mmmTripleComponentRowValid
    (key : List LColor) (expected : List Nat)
    (row : GoertzelLemma818TripleTauComponentSmoke.TripleComponentParentRow) :
    Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := GoertzelLemma818TripleTauComponentSmoke.tripleStates
      row.sourceLeft row.sourceMiddle row.sourceRight
    let t := GoertzelLemma818TripleTauComponentSmoke.tripleStates
      row.parentLeft row.parentMiddle row.parentRight
    compatibleChainStates mmmWord s && compatibleChainStates mmmWord t &&
      chainInputKey mmmWord s == key && chainInputKey mmmWord t == key &&
        (row.source == row.parent ||
          chainCertifiedKempeStep mmmWord s t row.cert)

def mmmFiber9SourcesCheck : Bool :=
  (mmmFiber9Rows.map fun row => row.source) == mmmFiber9Expected

theorem mmmFiber9SourcesCheck_ok :
    mmmFiber9SourcesCheck = true := by
  decide

def mmmFiber9RowCheck (i : Nat) : Bool :=
  mmmTripleComponentRowValid mmmFiber9Key mmmFiber9Expected
    (listGetD mmmFiber9Rows i default)

theorem mmmFiber9Row_0_ok : mmmFiber9RowCheck 0 = true := by decide
theorem mmmFiber9Row_1_ok : mmmFiber9RowCheck 1 = true := by decide
theorem mmmFiber9Row_2_ok : mmmFiber9RowCheck 2 = true := by decide
theorem mmmFiber9Row_3_ok : mmmFiber9RowCheck 3 = true := by decide
theorem mmmFiber9Row_4_ok : mmmFiber9RowCheck 4 = true := by decide
theorem mmmFiber9Row_5_ok : mmmFiber9RowCheck 5 = true := by decide
theorem mmmFiber9Row_6_ok : mmmFiber9RowCheck 6 = true := by decide
theorem mmmFiber9Row_7_ok : mmmFiber9RowCheck 7 = true := by decide
theorem mmmFiber9Row_8_ok : mmmFiber9RowCheck 8 = true := by decide
theorem mmmFiber9Row_9_ok : mmmFiber9RowCheck 9 = true := by decide
theorem mmmFiber9Row_10_ok : mmmFiber9RowCheck 10 = true := by decide
theorem mmmFiber9Row_11_ok : mmmFiber9RowCheck 11 = true := by decide
theorem mmmFiber9Row_12_ok : mmmFiber9RowCheck 12 = true := by decide
theorem mmmFiber9Row_13_ok : mmmFiber9RowCheck 13 = true := by decide
theorem mmmFiber9Row_14_ok : mmmFiber9RowCheck 14 = true := by decide
theorem mmmFiber9Row_15_ok : mmmFiber9RowCheck 15 = true := by decide

def mmmFiber9ParentCheck (i : Nat) : Bool :=
  GoertzelLemma818TripleTauComponentSmoke.tttFiber3ParentIter
      mmmFiber9Rows 6 (listGetD mmmFiber9Expected i 0) == 3808

theorem mmmFiber9Parent_0_ok : mmmFiber9ParentCheck 0 = true := by decide
theorem mmmFiber9Parent_1_ok : mmmFiber9ParentCheck 1 = true := by decide
theorem mmmFiber9Parent_2_ok : mmmFiber9ParentCheck 2 = true := by decide
theorem mmmFiber9Parent_3_ok : mmmFiber9ParentCheck 3 = true := by decide
theorem mmmFiber9Parent_4_ok : mmmFiber9ParentCheck 4 = true := by decide
theorem mmmFiber9Parent_5_ok : mmmFiber9ParentCheck 5 = true := by decide
theorem mmmFiber9Parent_6_ok : mmmFiber9ParentCheck 6 = true := by decide
theorem mmmFiber9Parent_7_ok : mmmFiber9ParentCheck 7 = true := by decide
theorem mmmFiber9Parent_8_ok : mmmFiber9ParentCheck 8 = true := by decide
theorem mmmFiber9Parent_9_ok : mmmFiber9ParentCheck 9 = true := by decide
theorem mmmFiber9Parent_10_ok : mmmFiber9ParentCheck 10 = true := by decide
theorem mmmFiber9Parent_11_ok : mmmFiber9ParentCheck 11 = true := by decide
theorem mmmFiber9Parent_12_ok : mmmFiber9ParentCheck 12 = true := by decide
theorem mmmFiber9Parent_13_ok : mmmFiber9ParentCheck 13 = true := by decide
theorem mmmFiber9Parent_14_ok : mmmFiber9ParentCheck 14 = true := by decide
theorem mmmFiber9Parent_15_ok : mmmFiber9ParentCheck 15 = true := by decide

def mmmFiber9ComponentCertificateAudit : Bool :=
  mmmRepresentativeModeSliceAudit &&
    mmmFiber9SourcesCheck &&
    mmmFiber9RowCheck 0 &&
    mmmFiber9RowCheck 1 &&
    mmmFiber9RowCheck 2 &&
    mmmFiber9RowCheck 3 &&
    mmmFiber9RowCheck 4 &&
    mmmFiber9RowCheck 5 &&
    mmmFiber9RowCheck 6 &&
    mmmFiber9RowCheck 7 &&
    mmmFiber9RowCheck 8 &&
    mmmFiber9RowCheck 9 &&
    mmmFiber9RowCheck 10 &&
    mmmFiber9RowCheck 11 &&
    mmmFiber9RowCheck 12 &&
    mmmFiber9RowCheck 13 &&
    mmmFiber9RowCheck 14 &&
    mmmFiber9RowCheck 15 &&
    mmmFiber9ParentCheck 0 &&
    mmmFiber9ParentCheck 1 &&
    mmmFiber9ParentCheck 2 &&
    mmmFiber9ParentCheck 3 &&
    mmmFiber9ParentCheck 4 &&
    mmmFiber9ParentCheck 5 &&
    mmmFiber9ParentCheck 6 &&
    mmmFiber9ParentCheck 7 &&
    mmmFiber9ParentCheck 8 &&
    mmmFiber9ParentCheck 9 &&
    mmmFiber9ParentCheck 10 &&
    mmmFiber9ParentCheck 11 &&
    mmmFiber9ParentCheck 12 &&
    mmmFiber9ParentCheck 13 &&
    mmmFiber9ParentCheck 14 &&
    mmmFiber9ParentCheck 15

theorem mmmFiber9ComponentCertificateAudit_ok :
    mmmFiber9ComponentCertificateAudit = true := by
  simp [mmmFiber9ComponentCertificateAudit,
    mmmRepresentativeModeSliceAudit_ok,
    mmmFiber9SourcesCheck_ok,
    mmmFiber9Row_0_ok,
    mmmFiber9Row_1_ok,
    mmmFiber9Row_2_ok,
    mmmFiber9Row_3_ok,
    mmmFiber9Row_4_ok,
    mmmFiber9Row_5_ok,
    mmmFiber9Row_6_ok,
    mmmFiber9Row_7_ok,
    mmmFiber9Row_8_ok,
    mmmFiber9Row_9_ok,
    mmmFiber9Row_10_ok,
    mmmFiber9Row_11_ok,
    mmmFiber9Row_12_ok,
    mmmFiber9Row_13_ok,
    mmmFiber9Row_14_ok,
    mmmFiber9Row_15_ok,
    mmmFiber9Parent_0_ok,
    mmmFiber9Parent_1_ok,
    mmmFiber9Parent_2_ok,
    mmmFiber9Parent_3_ok,
    mmmFiber9Parent_4_ok,
    mmmFiber9Parent_5_ok,
    mmmFiber9Parent_6_ok,
    mmmFiber9Parent_7_ok,
    mmmFiber9Parent_8_ok,
    mmmFiber9Parent_9_ok,
    mmmFiber9Parent_10_ok,
    mmmFiber9Parent_11_ok,
    mmmFiber9Parent_12_ok,
    mmmFiber9Parent_13_ok,
    mmmFiber9Parent_14_ok,
    mmmFiber9Parent_15_ok]

end GoertzelLemma818MirrorTripleComponentSmoke

end Mettapedia.GraphTheory.FourColor
