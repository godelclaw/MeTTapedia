import Mettapedia.GraphTheory.FourColor.CycleCapTangle

/-!
# The joint colour choice at two adjacent source vertices

Each endpoint avoids its two supplied exterior colours. If both pairs are
distinct, the endpoints are forced to their respective third colours; those
forced choices must still differ across their shared edge. A repeated exterior
pair leaves a choice at that endpoint. This is one law over the three-colour
alphabet, with no graph-specific colouring table.

The literal eight-cycle accepts a paired boundary word for which the two
endpoint choices clash. Consequently a replacement cannot forget the joint
seam constraint merely because each endpoint is separately colourable.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoice

/-- Two proper endpoint choices, including their shared source edge. -/
def Compatible (a b c d x y : Color) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ x ≠ a ∧ x ≠ b ∧ y ≠ c ∧ y ≠ d ∧ x ≠ y

/-- A repeated exterior pair permits a repair; otherwise the two forced
third colours must differ. The check concerns only the fixed colour alphabet. -/
theorem choices_iff (a b c d : Color) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (∃ x y, Compatible a b c d x y) ↔ a = b ∨ c = d ∨ a + b ≠ c + d := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with rfl | rfl | rfl <;>
    unfold Compatible <;> decide +kernel

theorem equal_forced_colours (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) : ¬∃ x y, Compatible a b a b x y := by
  rw [choices_iff a b a b ha hb ha hb]
  simp only [hab, false_or, ne_eq, not_true_eq_false, not_false_eq_true]

/-- The eight ports repeat each exterior observation twice in cyclic order. -/
def blockedWord (a b : Color) (i : Fin 8) : Color :=
  if i.val % 4 < 2 then a else b

def cycleEdges (a b : Color) (i : Fin 8) : Color :=
  if i.val % 4 = 0 then a + b
  else if i.val % 4 = 1 then b
  else if i.val % 4 = 2 then a + b else a

theorem cycle_valid (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    CycleCap.Valid 8 (cycleEdges a b) := by
  revert a b
  unfold CycleCap.Valid cycleEdges
  decide +kernel

theorem cycle_spokes (a b : Color) :
    CycleCap.spokes 8 (cycleEdges a b) = blockedWord a b := by
  funext i
  fin_cases i <;> simp [CycleCap.spokes, cycleEdges, blockedWord,
    add_comm, add_left_comm]
  all_goals rw [← add_assoc, color_add_self, zero_add]

/-- An actual eight-cycle colouring realizes the rejected paired profile. -/
theorem cycle_accepts (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (CycleCap.cap 8 (by decide)).AcceptsBoundaryWords Empty.elim (blockedWord a b) := by
  rw [← cycle_spokes]
  exact CycleCap.accepts_spokes 8 (by decide) (cycle_valid a b ha hb hab)

end Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoice
