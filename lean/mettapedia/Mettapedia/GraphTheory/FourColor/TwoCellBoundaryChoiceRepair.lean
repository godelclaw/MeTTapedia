import Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoice

/-! Changing one of the clashing paired observations to the third colour
permits explicit, compatible choices at both endpoints. This law concerns
the colour algebra only. A physical consumer must establish the operation
that changes that observation while preserving its exterior constraints. -/

namespace Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoice

/-- One changed pin removes the joint obstruction, with both interior
choices retained explicitly. -/
theorem repair_one_pin (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Compatible a (a+b) a b b (a+b) := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl
  all_goals first
    | exact (hab rfl).elim
    | unfold Compatible; decide +kernel

end Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoice
