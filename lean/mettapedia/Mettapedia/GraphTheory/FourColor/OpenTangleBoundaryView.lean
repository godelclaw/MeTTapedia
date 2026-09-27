import Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

/-!
# Forgetting the division of an open boundary

The input and output ports form one disjoint boundary carrier. This view
keeps every dart, vertex, edge mate and rotation unchanged. It connects the
serial colouring language to the geometric open-tangle library.
-/

namespace Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData

variable {V I L R : Type*}

@[simp] theorem asOpen_vertOf (T : TwoSidedOpenTangleData V I L R)
    (d : I ⊕ (L ⊕ R)) : (asOpen T).vertOf d = T.vertOf d := by
  rcases d with i | (l | r) <;> rfl

/-- The geometric view reads the same proper colouring on the same darts. -/
theorem asOpen_tait_iff (T : TwoSidedOpenTangleData V I L R) (c : T.Coloring) :
    ((∀ i, c (.inl ((asOpen T).interiorAlpha i)) = c (.inl i)) ∧
      (∀ {d e}, (asOpen T).vertOf d = (asOpen T).vertOf e → d ≠ e → c d ≠ c e) ∧
      ∀ d, c d ≠ 0) ↔ T.IsTaitColoring c := by
  simp only [asOpen_vertOf, IsTaitColoring]
  rfl

end Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer
