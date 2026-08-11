import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabConnectivityProfile

/-!
# A long-arc obstruction on a colored hexagon

A complete hexagonal face boundary contains two routes between the edges
flanking a distinguished boundary edge.  The long route may lie entirely in
one tracked two-color subgraph even when the distinguished edge carries the
third color.  Consequently, connectivity computed in a region containing the
whole face boundary cannot in general be recovered from only the two local
endpoint turns at the distinguished edge.

This finite witness concerns the choice of regional carrier.  It does not
refute the literal open-Cell profile or the source's relational transfer;
those use a different, smaller open region.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexBoundaryLongArcObstruction

open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24WindingClassification
open SimpleGraph

/-- The tracked part of a colored six-edge facial cycle, represented on its
six boundary-edge positions. -/
def trackedHexBoundaryGraph (word : Fin 6 → StrandColor) (a b : Color) :
    SimpleGraph (Fin 6) where
  Adj left right :=
    left ≠ right ∧
      (right = cyclicSucc left ∨ left = cyclicSucc right) ∧
      IsTrackedColor a b (word left).toColor ∧
      IsTrackedColor a b (word right).toColor
  symm := ⟨by
    rintro left right ⟨hne, hadj, hleft, hright⟩
    exact ⟨hne.symm, hadj.elim Or.inr Or.inl, hright, hleft⟩⟩
  loopless := ⟨by
    intro position hloop
    exact hloop.1 rfl⟩

instance trackedHexBoundaryGraphDecidableRel
    (word : Fin 6 → StrandColor) (a b : Color) :
    DecidableRel (trackedHexBoundaryGraph word a b).Adj :=
  fun left right => by
    change Decidable (left ≠ right ∧
      (right = cyclicSucc left ∨ left = cyclicSucc right) ∧
      IsTrackedColor a b (word left).toColor ∧
      IsTrackedColor a b (word right).toColor)
    infer_instance

/-- A proper boundary word whose edge at position zero has the third color,
while the complementary five-edge arc alternates between red and blue. -/
def longArcHexWord : Fin 6 → StrandColor :=
  ![.c, .a, .b, .a, .b, .a]

/-- The same word as a valid finite slab state with opposite distinguished
rungs. -/
def longArcHexState : HexSlabColorState :=
  ⟨0, 3, longArcHexWord⟩

theorem longArcHexState_valid : longArcHexState.Valid := by
  decide

theorem longArcHexWord_distinguished_not_redBlue :
    ¬ IsTrackedColor red blue (longArcHexWord 0).toColor := by
  decide

theorem longArcHexWord_other_positions_redBlue
    (position : Fin 6) (hne : position ≠ 0) :
    IsTrackedColor red blue (longArcHexWord position).toColor := by
  fin_cases position <;> simp_all [longArcHexWord, IsTrackedColor,
    StrandColor.toColor]

/-- The two facial edges flanking position zero are connected along the
complementary five-edge red-blue arc. -/
theorem longArcHexWord_flanks_reachable :
    (trackedHexBoundaryGraph longArcHexWord red blue).Reachable
      (cyclicSucc (0 : Fin 6)) (hexCyclicPred (0 : Fin 6)) := by
  decide

/-- The third-colored distinguished edge itself is absent from that tracked
component. -/
theorem longArcHexWord_distinguished_not_reachable_left :
    ¬ (trackedHexBoundaryGraph longArcHexWord red blue).Reachable
      (0 : Fin 6) (cyclicSucc (0 : Fin 6)) := by
  decide

theorem longArcHexWord_distinguished_not_reachable_right :
    ¬ (trackedHexBoundaryGraph longArcHexWord red blue).Reachable
      (0 : Fin 6) (hexCyclicPred (0 : Fin 6)) := by
  decide

/-- Proper Tait boundary coloring does not rule out a tracked connection
around the long side of a hexagon while the distinguished rung is untracked.
This is the finite obstruction to treating a complete face-boundary region as
if it carried only the two endpoint turns of that rung. -/
theorem exists_valid_hex_with_tracked_long_arc_avoiding_distinguished :
    ∃ state : HexSlabColorState,
      state.Valid ∧
        ¬ IsTrackedColor red blue (state.color state.incoming).toColor ∧
        (trackedHexBoundaryGraph state.color red blue).Reachable
          (cyclicSucc state.incoming) (hexCyclicPred state.incoming) ∧
        ¬ (trackedHexBoundaryGraph state.color red blue).Reachable
          state.incoming (cyclicSucc state.incoming) ∧
        ¬ (trackedHexBoundaryGraph state.color red blue).Reachable
          state.incoming (hexCyclicPred state.incoming) := by
  exact ⟨longArcHexState, longArcHexState_valid,
    longArcHexWord_distinguished_not_redBlue,
    longArcHexWord_flanks_reachable,
    longArcHexWord_distinguished_not_reachable_left,
    longArcHexWord_distinguished_not_reachable_right⟩

end GoertzelV24HexBoundaryLongArcObstruction

end Mettapedia.GraphTheory.FourColor
