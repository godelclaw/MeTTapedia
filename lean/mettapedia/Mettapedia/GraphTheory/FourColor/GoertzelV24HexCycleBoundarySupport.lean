import Mettapedia.GraphTheory.FourColor.GoertzelV24RawNooseCountPumping

/-!
# The six-port hex-cycle boundary recurrence

This file isolates the finite colour recurrence carried by a single hexagonal
cycle with one boundary port at every cycle vertex.  Starting with the colour
of the cycle edge entering vertex zero, crossing a port of colour `b` changes
the cycle-edge colour from `x` to `x + b`.  A boundary word extends across the
cycle exactly when the six resulting edge colours are nonzero and the final
local equation closes the cycle.

The executable definition below is accompanied by its ordinary existential
meaning.  The cardinality computation is deliberately tiny: it checks the
three possible starting colours against the `3 ^ 6` boundary words.  A later
module connects this recurrence to the literal `PortTangle` colouring fibre;
nothing here alone asserts that physical bridge.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCycleBoundarySupport

open GoertzelV24RawNooseCountPumping

/-- A computable enumeration of the three nonzero Klein colours. -/
def standardTaitColors : List TaitColor :=
  [⟨red, red_ne_zero⟩, ⟨blue, blue_ne_zero⟩, ⟨purple, purple_ne_zero⟩]

/-- Every Tait colour occurs in `standardTaitColors`. -/
theorem mem_standardTaitColors (start : TaitColor) :
    start ∈ standardTaitColors := by
  rcases start with ⟨start, hstart⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero start hstart with rfl | rfl | rfl <;>
    simp [standardTaitColors]

/-- Cyclic predecessor on the six cycle positions. -/
def hexPred (i : Fin 6) : Fin 6 := i - 1

/-- The cycle-edge colour after reading ports zero through `i`, with edge five
represented by the starting colour. -/
def hexEdgeFromStart (word : CutWord (Fin 6)) (start : Color) (i : Fin 6) : Color :=
  if i = 0 then start + (word 0).1 else
  if i = 1 then start + (word 0).1 + (word 1).1 else
  if i = 2 then start + (word 0).1 + (word 1).1 + (word 2).1 else
  if i = 3 then start + (word 0).1 + (word 1).1 + (word 2).1 + (word 3).1 else
  if i = 4 then start + (word 0).1 + (word 1).1 + (word 2).1 + (word 3).1 +
    (word 4).1 else
  start

/-- Ordinary mathematical meaning of the six-step recurrence. -/
def HexBoundaryRealizable (word : CutWord (Fin 6)) : Prop :=
  ∃ start : TaitColor, ∀ i,
    hexEdgeFromStart word start.1 i ≠ 0 ∧
      hexEdgeFromStart word start.1 (hexPred i) + (word i).1 +
        hexEdgeFromStart word start.1 i = 0

/-- Executable six-step recurrence test. -/
def hexBoundaryRealizableBool (word : CutWord (Fin 6)) : Bool :=
  standardTaitColors.any fun start =>
    (List.ofFn fun i : Fin 6 =>
      (hexEdgeFromStart word start.1 i != 0) &&
        (hexEdgeFromStart word start.1 (hexPred i) + (word i).1 +
          hexEdgeFromStart word start.1 i == 0)).all id

/-- The Boolean checker implements the existential recurrence literally. -/
theorem hexBoundaryRealizableBool_eq_true_iff (word : CutWord (Fin 6)) :
    hexBoundaryRealizableBool word = true ↔ HexBoundaryRealizable word := by
  simp only [hexBoundaryRealizableBool, List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨start, -, h⟩
    refine ⟨start, ?_⟩
    intro i
    have hi := h (hexEdgeFromStart word start.1 i != 0 &&
      (hexEdgeFromStart word start.1 (hexPred i) + (word i).1 +
        hexEdgeFromStart word start.1 i == 0))
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
    change
      ((hexEdgeFromStart word start.1 i != 0) &&
        (hexEdgeFromStart word start.1 (hexPred i) + (word i).1 +
          hexEdgeFromStart word start.1 i == 0)) = true at hi
    rcases Bool.and_eq_true_iff.mp hi with ⟨hi, heq⟩
    exact ⟨bne_iff_ne.mp hi, beq_iff_eq.mp heq⟩
  · rintro ⟨start, h⟩
    refine ⟨start, mem_standardTaitColors start, ?_⟩
    intro value hvalue
    rcases List.mem_ofFn.mp hvalue with ⟨i, rfl⟩
    rcases h i with ⟨hi, heq⟩
    change
      ((hexEdgeFromStart word start.1 i != 0) &&
        (hexEdgeFromStart word start.1 (hexPred i) + (word i).1 +
          hexEdgeFromStart word start.1 i == 0)) = true
    exact Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr hi, beq_iff_eq.mpr heq⟩

/-- The executable support of the six-step recurrence. -/
def hexCycleSupport : Finset (CutWord (Fin 6)) :=
  Finset.univ.filter fun word => hexBoundaryRealizableBool word = true

/-- **Exact recurrence census.**  Precisely 63 six-port boundary words pass. -/
theorem card_hexCycleSupport : hexCycleSupport.card = 63 := by
  decide

/-- Membership in the executable support has the ordinary recurrence meaning. -/
theorem mem_hexCycleSupport_iff (word : CutWord (Fin 6)) :
    word ∈ hexCycleSupport ↔ HexBoundaryRealizable word := by
  rw [hexCycleSupport, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact hexBoundaryRealizableBool_eq_true_iff word

end GoertzelV24HexCycleBoundarySupport

end Mettapedia.GraphTheory.FourColor
