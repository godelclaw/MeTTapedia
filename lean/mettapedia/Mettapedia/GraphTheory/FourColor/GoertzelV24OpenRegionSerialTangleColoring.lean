import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionColorGluing
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleColoring

/-!
# Reading an open-region coloring as a serial-tangle coloring

The literal open-region construction pairs every exposed old dart with a
fresh degree-one stub.  The serial open-tangle construction displays the same
old dart as an unpaired boundary port.  This file proves that forgetting the
fresh stubs and reindexing those ports preserves the complete open Tait
coloring semantics.

This is generic cut plumbing.  It neither chooses a source corridor nor
asserts that successive pieces have matching profiles.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionSerialTangleColoring

open GoertzelV24OpenRegionColorGluing
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenTangleComposition
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph

variable {V E L R : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Reading an old dart does not depend on which proof certifies that its
base vertex is retained. -/
theorem openOldDartColor_eq_of_dart_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : Dart RS keep)
    (coloring : (rotationSystem RS keep root).EdgeColoring Color)
    {left right : RS.D}
    (hleft : keep (RS.vertOf left)) (hright : keep (RS.vertOf right))
    (hdart : left = right) :
    openOldDartColor RS keep root coloring left hleft =
      openOldDartColor RS keep root coloring right hright := by
  subst right
  rfl

/-- Reassociate a split vertex-side open-tangle dart with its unique old
retained ambient dart. -/
noncomputable def splitVertexSideDartEquiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R) :
    InternalDart RS keep ⊕ (L ⊕ R) ≃ RetainedDart RS keep :=
  (OpenTangleData.boundarySplitDartEquiv
      (I := InternalDart RS keep) split).symm.trans
    (retainedDartEquivInternalSumBoundary RS keep).symm

@[simp]
theorem splitVertexSideDartEquiv_interior
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (dart : InternalDart RS keep) :
    splitVertexSideDartEquiv RS keep split (Sum.inl dart) = dart.1 :=
  rfl

@[simp]
theorem splitVertexSideDartEquiv_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (dart : L ⊕ R) :
    splitVertexSideDartEquiv RS keep split (Sum.inr dart) =
      (split.symm dart).1 :=
  rfl

/-- Read a literal open-region edge coloring on the corresponding split
serial open tangle.  Only old retained darts are read; the open region's
fresh stubs carry the same edge colors by construction. -/
noncomputable def splitVertexSideColoring
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring : (rotationSystem RS keep (Sum.inl root)).EdgeColoring Color) :
    ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).Coloring :=
  fun dart =>
    openOldDartColor RS keep (Sum.inl root) coloring
      (splitVertexSideDartEquiv RS keep split dart).1
      (splitVertexSideDartEquiv RS keep split dart).2

/-- The split tangle and the retained ambient dart expose the same old base
vertex. -/
@[simp]
theorem splitVertexSide_vertOf
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (dart : InternalDart RS keep ⊕ (L ⊕ R)) :
    (((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).vertOf
      dart).1 =
      RS.vertOf (splitVertexSideDartEquiv RS keep split dart).1 := by
  rcases dart with dart | (dart | dart) <;> rfl

/-- Internal edge mates retain one color after forgetting fresh stubs. -/
theorem splitVertexSideColoring_interiorAlpha
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring : (rotationSystem RS keep (Sum.inl root)).EdgeColoring Color)
    (dart : InternalDart RS keep) :
    splitVertexSideColoring RS keep root split coloring
        (Sum.inl
          (((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).interiorAlpha
            dart)) =
      splitVertexSideColoring RS keep root split coloring (Sum.inl dart) := by
  change
    openOldDartColor RS keep (Sum.inl root) coloring
        (RS.alpha dart.1.1) _ =
      openOldDartColor RS keep (Sum.inl root) coloring dart.1.1 _
  exact openOldDartColor_alpha_of_internal RS keep (Sum.inl root) coloring
    dart.1.1 dart.1.2 dart.2

/-- Reindexing cannot merge two darts at a retained vertex, so local
properness is inherited from the literal open-region coloring. -/
theorem splitVertexSideColoring_proper
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring : (rotationSystem RS keep (Sum.inl root)).EdgeColoring Color)
    {first second : InternalDart RS keep ⊕ (L ⊕ R)}
    (hvertex :
      ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).vertOf
          first =
        ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).vertOf
          second)
    (hne : first ≠ second) :
    splitVertexSideColoring RS keep root split coloring first ≠
      splitVertexSideColoring RS keep root split coloring second := by
  refine openOldDartColor_proper RS keep (Sum.inl root) coloring
    (left := (splitVertexSideDartEquiv RS keep split first).1)
    (right := (splitVertexSideDartEquiv RS keep split second).1)
    (splitVertexSideDartEquiv RS keep split first).2
    (splitVertexSideDartEquiv RS keep split second).2 ?_ ?_
  · have hvalue := congrArg Subtype.val hvertex
    simpa only [splitVertexSide_vertOf] using hvalue
  · intro hambient
    apply hne
    apply (splitVertexSideDartEquiv RS keep split).injective
    apply Subtype.ext
    exact hambient

/-- Every displayed serial-tangle dart remains nonzero. -/
theorem splitVertexSideColoring_ne_zero
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring : (rotationSystem RS keep (Sum.inl root)).EdgeColoring Color)
    (hcoloring :
      (rotationSystem RS keep (Sum.inl root)).IsTaitEdgeColoring coloring)
    (dart : InternalDart RS keep ⊕ (L ⊕ R)) :
    splitVertexSideColoring RS keep root split coloring dart ≠ 0 :=
  openOldDartColor_ne_zero RS keep (Sum.inl root) coloring hcoloring
    (splitVertexSideDartEquiv RS keep split dart).1
    (splitVertexSideDartEquiv RS keep split dart).2

/-- Forgetting the fresh degree-one stubs and splitting the exposed old
darts into input and output interfaces preserves literal Tait colorability. -/
theorem splitVertexSideColoring_isTait
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : RetainedDart RS keep)
    (split : BoundaryDart RS keep ≃ L ⊕ R)
    (coloring : (rotationSystem RS keep (Sum.inl root)).EdgeColoring Color)
    (hcoloring :
      (rotationSystem RS keep (Sum.inl root)).IsTaitEdgeColoring coloring) :
    ((OpenTangleData.ofVertexSide RS keep root).splitBoundary split).IsTaitColoring
        (splitVertexSideColoring RS keep root split coloring) := by
  constructor
  · exact splitVertexSideColoring_interiorAlpha RS keep root split coloring
  constructor
  · intro first second hvertex hne
    exact splitVertexSideColoring_proper RS keep root split coloring hvertex hne
  · exact splitVertexSideColoring_ne_zero RS keep root split coloring hcoloring

end

end GoertzelV24OpenRegionSerialTangleColoring

end Mettapedia.GraphTheory.FourColor
