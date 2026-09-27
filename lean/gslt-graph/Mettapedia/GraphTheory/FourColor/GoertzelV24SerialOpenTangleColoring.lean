import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleComposition
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

/-!
# Coloring semantics of serial open-tangle composition

An open tangle is colored on its literal darts.  Internal edge mates must
have equal colors, distinct darts at one vertex must have distinct colors,
and every color is nonzero.  Boundary darts are unpaired until composition.

This file proves the color-level functoriality required by the compositional
source: if the output colors of one tangle agree with the matched input
colors of the next, their serial composite has a proper open Tait coloring.
The external input and output words are preserved exactly.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleComposition

noncomputable section

namespace TwoSidedOpenTangleData

variable {V W I L R J M S : Type*}

/-- A coloring of the literal darts of a two-sided open tangle. -/
abbrev Coloring (_data : TwoSidedOpenTangleData V I L R) :=
  I ⊕ (L ⊕ R) → Color

/-- Open Tait-coloring semantics.  Internal edge mates have one color,
different darts at a common vertex are properly colored, and all colors are
nonzero.  Boundary darts remain unpaired and therefore have no edge-mate
equation until they are glued. -/
def IsTaitColoring (data : TwoSidedOpenTangleData V I L R)
    (coloring : data.Coloring) : Prop :=
  (∀ dart : I,
      coloring (Sum.inl (data.interiorAlpha dart)) = coloring (Sum.inl dart)) ∧
  (∀ {first second : I ⊕ (L ⊕ R)},
      data.vertOf first = data.vertOf second → first ≠ second →
        coloring first ≠ coloring second) ∧
  ∀ dart, coloring dart ≠ 0

/-- The displayed input-boundary color word. -/
def leftBoundaryColor (data : TwoSidedOpenTangleData V I L R)
    (coloring : data.Coloring) (dart : L) : Color :=
  coloring (Sum.inr (Sum.inl dart))

/-- The displayed output-boundary color word. -/
def rightBoundaryColor (data : TwoSidedOpenTangleData V I L R)
    (coloring : data.Coloring) (dart : R) : Color :=
  coloring (Sum.inr (Sum.inr dart))

/-- The two source colorings before carrier reassociation. -/
def serialSourceColor
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring) :
    (I ⊕ (L ⊕ R)) ⊕ (J ⊕ (M ⊕ S)) → Color
  | Sum.inl dart => leftColoring dart
  | Sum.inr dart => rightColoring dart

/-- Reassociate a pair of open colorings onto the serial-composite dart
carrier. -/
def serialColor
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring) :
    (((I ⊕ J) ⊕ (R ⊕ M)) ⊕ (L ⊕ S)) → Color :=
  fun dart => serialSourceColor left right leftColoring rightColoring
    (serialDartEquiv.symm dart)

/-- The exact compatibility condition for the newly paired seam. -/
def SeamColorAgreement
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring) : Prop :=
  ∀ dart : R,
    left.rightBoundaryColor leftColoring dart =
      right.leftBoundaryColor rightColoring (matching dart)

/-- Properness of the two source colorings on the tagged disjoint union of
their vertex carriers. -/
theorem serialSourceColor_proper
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring)
    (hleft : left.IsTaitColoring leftColoring)
    (hright : right.IsTaitColoring rightColoring)
    {first second : (I ⊕ (L ⊕ R)) ⊕ (J ⊕ (M ⊕ S))}
    (hvertex : serialSourceVertOf left right first =
      serialSourceVertOf left right second)
    (hne : first ≠ second) :
    serialSourceColor left right leftColoring rightColoring first ≠
      serialSourceColor left right leftColoring rightColoring second := by
  rcases first with first | first <;> rcases second with second | second
  · simpa [serialSourceColor, serialSourceVertOf] using
      hleft.2.1 (Sum.inl.inj hvertex)
        (fun heq => hne (congrArg Sum.inl heq))
  · simp [serialSourceVertOf] at hvertex
  · simp [serialSourceVertOf] at hvertex
  · simpa [serialSourceColor, serialSourceVertOf] using
      hright.2.1 (Sum.inr.inj hvertex)
        (fun heq => hne (congrArg Sum.inr heq))

/-- The serial color is constant on every internal edge.  On old edges this
comes from the source colorings; on the new seam it is precisely the seam
agreement hypothesis. -/
theorem serialColor_interiorAlpha
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring)
    (hleft : left.IsTaitColoring leftColoring)
    (hright : right.IsTaitColoring rightColoring)
    (hagreement : SeamColorAgreement left right matching
      leftColoring rightColoring)
    (dart : (I ⊕ J) ⊕ (R ⊕ M)) :
    serialColor left right leftColoring rightColoring
        (Sum.inl (serialInteriorAlpha left right matching dart)) =
      serialColor left right leftColoring rightColoring (Sum.inl dart) := by
  rcases dart with (dart | dart) | (dart | dart)
  · simpa [serialColor, serialSourceColor, serialDartEquiv,
      serialInteriorAlpha] using hleft.1 dart
  · simpa [serialColor, serialSourceColor, serialDartEquiv,
      serialInteriorAlpha] using hright.1 dart
  · simpa [serialColor, serialSourceColor, serialDartEquiv,
      serialInteriorAlpha, SeamColorAgreement, leftBoundaryColor,
      rightBoundaryColor] using (hagreement dart).symm
  · simpa [serialColor, serialSourceColor, serialDartEquiv,
      serialInteriorAlpha, SeamColorAgreement, leftBoundaryColor,
      rightBoundaryColor] using hagreement (matching.symm dart)

/-- Properness survives serial composition.  Tagged vertex carriers rule out
new cross-piece vertex collisions. -/
theorem serialColor_proper
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring)
    (hleft : left.IsTaitColoring leftColoring)
    (hright : right.IsTaitColoring rightColoring)
    {first second : (((I ⊕ J) ⊕ (R ⊕ M)) ⊕ (L ⊕ S))}
    (hvertex : serialOutputVertOf left right first =
      serialOutputVertOf left right second)
    (hne : first ≠ second) :
    serialColor left right leftColoring rightColoring first ≠
      serialColor left right leftColoring rightColoring second := by
  let equiv := serialDartEquiv
    (I := I) (L := L) (R := R) (J := J) (M := M) (S := S)
  have hfirst : serialOutputVertOf left right first =
      serialSourceVertOf left right (equiv.symm first) := by
    simpa [equiv] using
      serialOutputVertOf_serialDartEquiv left right (equiv.symm first)
  have hsecond : serialOutputVertOf left right second =
      serialSourceVertOf left right (equiv.symm second) := by
    simpa [equiv] using
      serialOutputVertOf_serialDartEquiv left right (equiv.symm second)
  have hsourceVertex :
      serialSourceVertOf left right (equiv.symm first) =
        serialSourceVertOf left right (equiv.symm second) :=
    hfirst.symm.trans (hvertex.trans hsecond)
  have hsourceNe : equiv.symm first ≠ equiv.symm second := by
    intro heq
    exact hne (equiv.symm.injective heq)
  exact serialSourceColor_proper left right leftColoring rightColoring
    hleft hright hsourceVertex hsourceNe

/-- Every serial-composite dart keeps a nonzero source color. -/
theorem serialColor_ne_zero
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring)
    (hleft : left.IsTaitColoring leftColoring)
    (hright : right.IsTaitColoring rightColoring)
    (dart : (((I ⊕ J) ⊕ (R ⊕ M)) ⊕ (L ⊕ S))) :
    serialColor left right leftColoring rightColoring dart ≠ 0 := by
  let equiv := serialDartEquiv
    (I := I) (L := L) (R := R) (J := J) (M := M) (S := S)
  rcases hsource : equiv.symm dart with source | source
  · simpa [serialColor, serialSourceColor, equiv, hsource] using
      hleft.2.2 source
  · simpa [serialColor, serialSourceColor, equiv, hsource] using
      hright.2.2 source

/-- Color-level functoriality of serial composition. -/
theorem serialColor_isTait
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring)
    (hleft : left.IsTaitColoring leftColoring)
    (hright : right.IsTaitColoring rightColoring)
    (hagreement : SeamColorAgreement left right matching
      leftColoring rightColoring) :
    (serialCompose left right matching).IsTaitColoring
      (serialColor left right leftColoring rightColoring) := by
  refine ⟨serialColor_interiorAlpha left right matching leftColoring
    rightColoring hleft hright hagreement, ?_,
    serialColor_ne_zero left right leftColoring rightColoring hleft hright⟩
  intro first second hvertex hne
  apply serialColor_proper left right leftColoring rightColoring hleft hright
    ?_ hne
  calc
    serialOutputVertOf left right first =
        twoSidedOpenTangleVertOf
          (fun dart => serialOutputVertOf left right (Sum.inl dart))
          (fun dart => serialOutputVertOf left right (Sum.inr (Sum.inl dart)))
          (fun dart => serialOutputVertOf left right (Sum.inr (Sum.inr dart)))
          first := (twoSidedOpenTangleVertOf_serialOutput left right first).symm
    _ = twoSidedOpenTangleVertOf
          (fun dart => serialOutputVertOf left right (Sum.inl dart))
          (fun dart => serialOutputVertOf left right (Sum.inr (Sum.inl dart)))
          (fun dart => serialOutputVertOf left right (Sum.inr (Sum.inr dart)))
          second := hvertex
    _ = serialOutputVertOf left right second :=
      twoSidedOpenTangleVertOf_serialOutput left right second

/-- Serial composition preserves the first tangle's input word. -/
@[simp]
theorem serialColor_leftBoundaryColor
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring)
    (dart : L) :
    (serialCompose left right matching).leftBoundaryColor
        (serialColor left right leftColoring rightColoring) dart =
      left.leftBoundaryColor leftColoring dart := by
  rfl

/-- Serial composition preserves the second tangle's output word. -/
@[simp]
theorem serialColor_rightBoundaryColor
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M)
    (leftColoring : left.Coloring) (rightColoring : right.Coloring)
    (dart : S) :
    (serialCompose left right matching).rightBoundaryColor
        (serialColor left right leftColoring rightColoring) dart =
      right.rightBoundaryColor rightColoring dart := by
  rfl

end TwoSidedOpenTangleData

end

end GoertzelV24OpenTangleComposition

end Mettapedia.GraphTheory.FourColor
