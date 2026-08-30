import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Exact zero-Count semantics for a closed rotation system

The direct compositional route calls a closed map `zero Count` precisely when
it has no proper nonzero Tait edge colouring.  This file makes that convention
literal: the count is the finite cardinality of the type of Tait colourings,
and vanishing is equivalent to non-colourability.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationTaitCount

open GoertzelV24TwoEdgeCutMinimality

noncomputable section

universe u v

variable {V : Type u} {E : Type v}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The finite type of proper nonzero Tait edge colourings of a closed
rotation system. -/
def TaitColoring (RS : RotationSystem V E) :=
  {coloring : RS.EdgeColoring Color // RS.IsTaitEdgeColoring coloring}

/-- The exact closed Tait count used by the reductive route. -/
def rotationSystemTaitCount (RS : RotationSystem V E) : Nat :=
  Nat.card (TaitColoring RS)

/-- Positive Count is exactly Tait colourability. -/
theorem rotationSystemTaitCount_pos_iff (RS : RotationSystem V E) :
    0 < rotationSystemTaitCount RS ↔ RotationSystemTaitColorable RS := by
  letI : Finite (TaitColoring RS) := by
    apply Finite.of_injective
      (fun coloring : TaitColoring RS => fun edge : E => coloring.1 edge)
    intro left right heq
    apply Subtype.ext
    apply DFunLike.ext _ _
    intro edge
    exact congrFun heq edge
  rw [rotationSystemTaitCount, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨coloring, hcoloring⟩⟩
    exact ⟨coloring, hcoloring⟩
  · rintro ⟨coloring, hcoloring⟩
    exact ⟨⟨⟨coloring, hcoloring⟩⟩, inferInstance⟩

/-- Zero Count is exactly failure of Tait colourability. -/
theorem rotationSystemTaitCount_eq_zero_iff (RS : RotationSystem V E) :
    rotationSystemTaitCount RS = 0 ↔ ¬ RotationSystemTaitColorable RS := by
  rw [← not_iff_not]
  simpa [Nat.pos_iff_ne_zero] using rotationSystemTaitCount_pos_iff RS

end

end GoertzelV24RotationTaitCount

end Mettapedia.GraphTheory.FourColor
