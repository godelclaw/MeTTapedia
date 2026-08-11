import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionSerialTangleColoring

/-!
# Reconstructing an open-region coloring from a serial tangle

The forward adapter forgets each fresh degree-one boundary stub and displays
its old mate as an unpaired serial port.  This file proves the inverse
coloring construction: give the fresh stub the same color as that port, then
descend the resulting alpha-invariant dart coloring to the literal open
region's edge carrier.

Together the two adapters give exact support semantics, not merely a map in
the easy direction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionSerialTangleColoring

open GoertzelV24OpenRegionRotation
open GoertzelV24OpenTangleComposition
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationDartColoring
open SimpleGraph

variable {V E L R : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Send every literal open-region dart to its displayed serial-tangle dart.
An exposed old dart and its fresh stub deliberately have the same image. -/
noncomputable def splitVertexSideOpenRegionDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R) :
    Dart RS keep → InternalDart RS keep ⊕ (L ⊕ R)
  | Sum.inl retained => (splitVertexSideDartEquiv RS keep split).symm retained
  | Sum.inr boundary => Sum.inr (split boundary)

@[simp]
theorem splitVertexSideOpenRegionDart_old_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (dart : InternalDart RS keep) :
    splitVertexSideOpenRegionDart RS keep split (Sum.inl dart.1) =
      Sum.inl dart := by
  change (splitVertexSideDartEquiv RS keep split).symm dart.1 = Sum.inl dart
  apply (splitVertexSideDartEquiv RS keep split).injective
  rw [Equiv.apply_symm_apply, splitVertexSideDartEquiv_interior]

@[simp]
theorem splitVertexSideOpenRegionDart_old_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (dart : BoundaryDart RS keep) :
    splitVertexSideOpenRegionDart RS keep split (Sum.inl dart.1) =
      Sum.inr (split dart) := by
  change (splitVertexSideDartEquiv RS keep split).symm dart.1 =
    Sum.inr (split dart)
  apply (splitVertexSideDartEquiv RS keep split).injective
  rw [Equiv.apply_symm_apply, splitVertexSideDartEquiv_boundary,
    Equiv.symm_apply_apply]

@[simp]
theorem splitVertexSideOpenRegionDart_stub
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (dart : BoundaryDart RS keep) :
    splitVertexSideOpenRegionDart RS keep split (Sum.inr dart) =
      Sum.inr (split dart) :=
  rfl

/-- Pull a serial-tangle coloring back to the dart carrier of the literal
open region. -/
noncomputable def openRegionDartColorOfSplitVertexSideColoring
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring : InternalDart RS keep ⊕ (L ⊕ R) → Color) :
    Dart RS keep → Color :=
  fun dart => coloring (splitVertexSideOpenRegionDart RS keep split dart)

/-- The pulled-back dart color is constant across every literal open-region
edge, including the old-dart/fresh-stub boundary pairs. -/
theorem openRegionDartColorOfSplitVertexSideColoring_alpha
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring)
    (hcoloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        coloring)
    (dart : (rotationSystem RS keep (Sum.inl root)).D) :
    openRegionDartColorOfSplitVertexSideColoring RS keep split coloring
        ((rotationSystem RS keep (Sum.inl root)).alpha dart) =
      openRegionDartColorOfSplitVertexSideColoring RS keep split coloring dart := by
  rcases dart with retained | boundary
  · by_cases hinternal : keep (RS.vertOf (RS.alpha retained.1))
    · let internal : InternalDart RS keep := ⟨retained, hinternal⟩
      rw [rotationSystem_alpha_old_of_internal RS keep (Sum.inl root)
        retained hinternal]
      unfold openRegionDartColorOfSplitVertexSideColoring
      have hleft :
          (⟨RS.alpha retained.1, hinternal⟩ : RetainedDart RS keep) =
            (internalAlpha RS keep internal).1 := by
        apply Subtype.ext
        rfl
      have hright : retained = internal.1 := rfl
      rw [hleft, hright, splitVertexSideOpenRegionDart_old_internal,
        splitVertexSideOpenRegionDart_old_internal]
      exact hcoloring.1 internal
    · let exposed : BoundaryDart RS keep := ⟨retained, hinternal⟩
      rw [rotationSystem_alpha_old_of_boundary RS keep (Sum.inl root)
        retained hinternal]
      change coloring (Sum.inr (split exposed)) =
        coloring (splitVertexSideOpenRegionDart RS keep split (Sum.inl exposed.1))
      rw [splitVertexSideOpenRegionDart_old_boundary]
  · rw [rotationSystem_alpha_stub]
    simp [openRegionDartColorOfSplitVertexSideColoring]

/-- At old vertices, properness is transported through the retained-dart
equivalence; a fresh stub vertex has only its single dart. -/
theorem openRegionDartColorOfSplitVertexSideColoring_proper
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring)
    (hcoloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        coloring)
    {left right : (rotationSystem RS keep (Sum.inl root)).D}
    (hvertex :
      (rotationSystem RS keep (Sum.inl root)).vertOf left =
        (rotationSystem RS keep (Sum.inl root)).vertOf right)
    (hne : left ≠ right) :
    openRegionDartColorOfSplitVertexSideColoring RS keep split coloring left ≠
      openRegionDartColorOfSplitVertexSideColoring RS keep split coloring right := by
  rcases left with left | left <;> rcases right with right | right
  · apply hcoloring.2.1
    · apply Subtype.ext
      simpa [splitVertexSideOpenRegionDart] using
        congrArg Subtype.val (Sum.inl.inj hvertex)
    · intro hdart
      apply hne
      apply congrArg Sum.inl
      have hretained := congrArg (splitVertexSideDartEquiv RS keep split) hdart
      simpa [splitVertexSideOpenRegionDart] using hretained
  · cases hvertex
  · cases hvertex
  · have hboundary : left = right := Sum.inr.inj hvertex
    exact (hne (congrArg Sum.inr hboundary)).elim

/-- The pulled-back dart coloring is nonzero everywhere. -/
theorem openRegionDartColorOfSplitVertexSideColoring_ne_zero
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring)
    (hcoloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        coloring)
    (dart : (rotationSystem RS keep (Sum.inl root)).D) :
    openRegionDartColorOfSplitVertexSideColoring RS keep split coloring dart ≠ 0 :=
  hcoloring.2.2 (splitVertexSideOpenRegionDart RS keep split dart)

/-- Descend a serial open-tangle coloring to the literal open-region edge
carrier after restoring equal colors on every fresh stub. -/
noncomputable def openRegionColoringOfSplitVertexSideColoring
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring)
    (hcoloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        coloring) :
    (rotationSystem RS keep (Sum.inl root)).EdgeColoring Color :=
  edgeColoringOfDartColor (rotationSystem RS keep (Sum.inl root))
    (openRegionDartColorOfSplitVertexSideColoring RS keep split coloring)
    (openRegionDartColorOfSplitVertexSideColoring_alpha RS keep root split
      coloring hcoloring)
    (openRegionDartColorOfSplitVertexSideColoring_proper RS keep root split
      coloring hcoloring)

/-- The reconstructed literal open-region edge coloring is Tait. -/
theorem openRegionColoringOfSplitVertexSideColoring_isTait
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring)
    (hcoloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        coloring) :
    (rotationSystem RS keep (Sum.inl root)).IsTaitEdgeColoring
      (openRegionColoringOfSplitVertexSideColoring RS keep root split coloring
        hcoloring) :=
  edgeColoringOfDartColor_isTait (rotationSystem RS keep (Sum.inl root))
    (openRegionDartColorOfSplitVertexSideColoring RS keep split coloring)
    (openRegionDartColorOfSplitVertexSideColoring_alpha RS keep root split
      coloring hcoloring)
    (openRegionDartColorOfSplitVertexSideColoring_proper RS keep root split
      coloring hcoloring)
    (openRegionDartColorOfSplitVertexSideColoring_ne_zero RS keep root split
      coloring hcoloring)

/-- Reading the reconstructed open-region coloring at an old retained dart
recovers the original serial-tangle color exactly. -/
theorem openRegionColoringOfSplitVertexSideColoring_openOldDartColor
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring)
    (hcoloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        coloring)
    (dart : RetainedDart RS keep) :
    GoertzelV24OpenRegionColorGluing.openOldDartColor RS keep (Sum.inl root)
        (openRegionColoringOfSplitVertexSideColoring RS keep root split coloring
          hcoloring) dart.1 dart.2 =
      coloring ((splitVertexSideDartEquiv RS keep split).symm dart) := by
  unfold GoertzelV24OpenRegionColorGluing.openOldDartColor
  exact edgeColoringOfDartColor_edgeOf
    (rotationSystem RS keep (Sum.inl root))
    (openRegionDartColorOfSplitVertexSideColoring RS keep split coloring)
    (openRegionDartColorOfSplitVertexSideColoring_alpha RS keep root split
      coloring hcoloring)
    (openRegionDartColorOfSplitVertexSideColoring_proper RS keep root split
      coloring hcoloring) (Sum.inl dart)

/-- Reconstructing the literal open-region coloring and reading it back on
the split serial carrier returns the original serial coloring.  This is the
support-level inverse to `splitVertexSideColoring`; no counting argument is
involved. -/
theorem splitVertexSideColoring_openRegionColoringOfSplitVertexSideColoring
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring)
    (hcoloring :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        coloring) :
    splitVertexSideColoring RS keep root split
        (openRegionColoringOfSplitVertexSideColoring RS keep root split coloring
          hcoloring) =
      coloring := by
  funext dart
  unfold splitVertexSideColoring
  rw [openRegionColoringOfSplitVertexSideColoring_openOldDartColor]
  simp

end

end GoertzelV24OpenRegionSerialTangleColoring

end Mettapedia.GraphTheory.FourColor
