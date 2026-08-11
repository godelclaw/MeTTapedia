import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleColoring

/-!
# Support-level `Count` composition for open tangles

The source's `Count` functor sends a serial composite to matrix
multiplication.  At support level, this says that the composite accepts its
two exterior boundary words exactly when there is a middle word accepted by
both factors.  This file proves that statement directly from literal open
colorings.

The theorem is bidirectional: forward restriction recovers the two factor
colorings and their common seam word, while backward gluing uses the
color-level serial-composition theorem.  No profile equality or finite audit
is assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleComposition

noncomputable section

namespace TwoSidedOpenTangleData

variable {V W I L R J M S : Type*}

/-- The original left coloring recovered from a coloring of a serial
composite. -/
def leftRestriction
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (coloring : (serialCompose left right matching).Coloring) : left.Coloring :=
  fun dart => coloring (serialDartEquiv (Sum.inl dart))

/-- The original right coloring recovered from a coloring of a serial
composite. -/
def rightRestriction
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (coloring : (serialCompose left right matching).Coloring) : right.Coloring :=
  fun dart => coloring (serialDartEquiv (Sum.inr dart))

/-- The serial carrier equivalence preserves the displayed tagged vertex. -/
@[simp]
theorem serialCompose_vertOf_serialDartEquiv
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (dart : (I ⊕ (L ⊕ R)) ⊕ (J ⊕ (M ⊕ S))) :
    (serialCompose left right matching).vertOf (serialDartEquiv dart) =
      serialSourceVertOf left right dart := by
  change twoSidedOpenTangleVertOf
      (fun interior => serialOutputVertOf left right (Sum.inl interior))
      (fun leftBoundary => serialOutputVertOf left right
        (Sum.inr (Sum.inl leftBoundary)))
      (fun rightBoundary => serialOutputVertOf left right
        (Sum.inr (Sum.inr rightBoundary))) (serialDartEquiv dart) = _
  rw [twoSidedOpenTangleVertOf_serialOutput,
    serialOutputVertOf_serialDartEquiv]

/-- Restricting a composite open Tait coloring to its left source piece
preserves every open-coloring obligation. -/
theorem leftRestriction_isTait
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (coloring : (serialCompose left right matching).Coloring)
    (hcoloring : (serialCompose left right matching).IsTaitColoring coloring) :
    left.IsTaitColoring (leftRestriction left right matching coloring) := by
  refine ⟨?_, ?_, ?_⟩
  · intro dart
    simpa [leftRestriction, serialCompose, serialInteriorAlpha,
      serialDartEquiv] using hcoloring.1 (Sum.inl (Sum.inl dart))
  · intro first second hvertex hne
    apply hcoloring.2.1
    · simpa [serialSourceVertOf] using
        congrArg (fun vertex : V => (Sum.inl vertex : V ⊕ W)) hvertex
    · intro heq
      apply hne
      exact Sum.inl.inj (serialDartEquiv.injective heq)
  · intro dart
    exact hcoloring.2.2 (serialDartEquiv (Sum.inl dart))

/-- Restricting a composite open Tait coloring to its right source piece
preserves every open-coloring obligation. -/
theorem rightRestriction_isTait
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (coloring : (serialCompose left right matching).Coloring)
    (hcoloring : (serialCompose left right matching).IsTaitColoring coloring) :
    right.IsTaitColoring (rightRestriction left right matching coloring) := by
  refine ⟨?_, ?_, ?_⟩
  · intro dart
    simpa [rightRestriction, serialCompose, serialInteriorAlpha,
      serialDartEquiv] using hcoloring.1 (Sum.inl (Sum.inr dart))
  · intro first second hvertex hne
    apply hcoloring.2.1
    · simpa [serialSourceVertOf] using
        congrArg (fun vertex : W => (Sum.inr vertex : V ⊕ W)) hvertex
    · intro heq
      apply hne
      exact Sum.inr.inj (serialDartEquiv.injective heq)
  · intro dart
    exact hcoloring.2.2 (serialDartEquiv (Sum.inr dart))

/-- The two restrictions of a composite coloring agree on the seam paired by
the serial matching. -/
theorem restrictions_seamColorAgreement
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (coloring : (serialCompose left right matching).Coloring)
    (hcoloring : (serialCompose left right matching).IsTaitColoring coloring) :
    SeamColorAgreement left right matching
      (leftRestriction left right matching coloring)
      (rightRestriction left right matching coloring) := by
  intro dart
  simpa [leftRestriction, rightRestriction, leftBoundaryColor,
    rightBoundaryColor, serialCompose, serialInteriorAlpha,
    serialDartEquiv] using
      (hcoloring.1 (Sum.inr (Sum.inl dart))).symm

/-- Restriction reads the composite's exterior input word. -/
@[simp]
theorem leftRestriction_leftBoundaryColor
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (coloring : (serialCompose left right matching).Coloring)
    (dart : L) :
    left.leftBoundaryColor (leftRestriction left right matching coloring) dart =
      (serialCompose left right matching).leftBoundaryColor coloring dart := by
  rfl

/-- Restriction reads the composite's exterior output word. -/
@[simp]
theorem rightRestriction_rightBoundaryColor
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (coloring : (serialCompose left right matching).Coloring)
    (dart : S) :
    right.rightBoundaryColor (rightRestriction left right matching coloring) dart =
      (serialCompose left right matching).rightBoundaryColor coloring dart := by
  rfl

/-- Support of one `Count` entry: an open Tait coloring realizing the given
input and output boundary words. -/
def AcceptsBoundaryWords
    (data : TwoSidedOpenTangleData V I L R)
    (leftWord : L → Color) (rightWord : R → Color) : Prop :=
  ∃ coloring : data.Coloring,
    data.IsTaitColoring coloring ∧
      data.leftBoundaryColor coloring = leftWord ∧
      data.rightBoundaryColor coloring = rightWord

/-- Support-level matrix multiplication for literal serial composition. -/
theorem serialCompose_acceptsBoundaryWords_iff
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (leftWord : L → Color) (rightWord : S → Color) :
    (serialCompose left right matching).AcceptsBoundaryWords
        leftWord rightWord ↔
      ∃ middle : R → Color,
        left.AcceptsBoundaryWords leftWord middle ∧
        right.AcceptsBoundaryWords
          (fun dart => middle (matching.symm dart)) rightWord := by
  constructor
  · rintro ⟨coloring, hcoloring, hleftWord, hrightWord⟩
    let leftColoring := leftRestriction left right matching coloring
    let rightColoring := rightRestriction left right matching coloring
    let middle := left.rightBoundaryColor leftColoring
    have hagreement := restrictions_seamColorAgreement left right matching
      coloring hcoloring
    refine ⟨middle, ⟨leftColoring, ?_, ?_, rfl⟩,
      ⟨rightColoring, ?_, ?_, ?_⟩⟩
    · exact leftRestriction_isTait left right matching coloring hcoloring
    · funext dart
      exact congrFun hleftWord dart
    · exact rightRestriction_isTait left right matching coloring hcoloring
    · funext dart
      have hseam := hagreement (matching.symm dart)
      simpa [middle] using hseam.symm
    · funext dart
      exact congrFun hrightWord dart
  · rintro ⟨middle, ⟨leftColoring, hleft, hleftWord, hmiddle⟩,
      ⟨rightColoring, hright, hmiddleRight, hrightWord⟩⟩
    have hagreement : SeamColorAgreement left right matching
        leftColoring rightColoring := by
      intro dart
      rw [congrFun hmiddle dart, congrFun hmiddleRight (matching dart)]
      simp
    let coloring := serialColor left right leftColoring rightColoring
    refine ⟨coloring,
      serialColor_isTait left right matching leftColoring rightColoring
        hleft hright hagreement, ?_, ?_⟩
    · funext dart
      simpa [coloring] using congrFun hleftWord dart
    · funext dart
      simpa [coloring] using congrFun hrightWord dart

end TwoSidedOpenTangleData

end

end GoertzelV24OpenTangleComposition

end Mettapedia.GraphTheory.FourColor
