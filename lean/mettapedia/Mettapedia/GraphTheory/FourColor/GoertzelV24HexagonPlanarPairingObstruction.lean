import Mettapedia.GraphTheory.FourColor.GoertzelV24Square

/-!
# A hexagon is not a positive sum of its planar pairing caps

The facial-square reduction works because the proper-colouring fibre of a
four-cycle is exactly the disjoint sum of the fibres of its two noncrossing
pairing caps.  The analogous statement already fails for a six-cycle.

This module records the smallest literal obstruction.  The cyclic boundary
word `red, blue, purple, red, blue, purple` extends across the hexagon, but no
noncrossing perfect matching of the six ports joins equal colours.  Therefore
no choice of nonnegative multiplicities on the five planar pairing caps can
recover the hexagon extension count.  This is a boundary-semantic obstruction;
it does not depend on an ambient graph or on a choice of connectivity profile.
-/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The six outer colours of a hexagon, in cyclic order. -/
abbrev HexagonBoundaryWord := Fin 6 → Color

/-- Colours of the six hexagon edges, in cyclic order. -/
abbrev HexagonInternalColoring := Fin 6 → Color

/-- The exact local properness test for extending six outer colours across a
hexagon.  Internal edge `i` joins the vertices at boundary positions `i` and
`i+1`, cyclically. -/
def IsHexagonExtension
    (w : HexagonBoundaryWord) (x : HexagonInternalColoring) : Prop :=
  ProperColorTriple (w 0) (x 5) (x 0) ∧
  ProperColorTriple (w 1) (x 0) (x 1) ∧
  ProperColorTriple (w 2) (x 1) (x 2) ∧
  ProperColorTriple (w 3) (x 2) (x 3) ∧
  ProperColorTriple (w 4) (x 3) (x 4) ∧
  ProperColorTriple (w 5) (x 4) (x 5)
  deriving Decidable

/-- All proper internal colourings extending a fixed hexagon boundary word. -/
def hexagonExtensions
    (w : HexagonBoundaryWord) : Finset HexagonInternalColoring :=
  Finset.univ.filter (IsHexagonExtension w)

@[simp] theorem mem_hexagonExtensions_iff
    {w : HexagonBoundaryWord} {x : HexagonInternalColoring} :
    x ∈ hexagonExtensions w ↔ IsHexagonExtension w x := by
  simp [hexagonExtensions]

/-- The five noncrossing perfect matchings of six cyclically ordered ports. -/
abbrev HexagonPlanarPairing := Fin 5

namespace HexagonPlanarPairing

/-- A planar pairing cap is colour-compatible when each joined pair of ports
has equal boundary colours. -/
def Compatible (side : HexagonPlanarPairing)
    (w : HexagonBoundaryWord) : Prop :=
  if side = 0 then
    w 0 = w 1 ∧ w 2 = w 3 ∧ w 4 = w 5
  else if side = 1 then
    w 0 = w 1 ∧ w 2 = w 5 ∧ w 3 = w 4
  else if side = 2 then
    w 0 = w 3 ∧ w 1 = w 2 ∧ w 4 = w 5
  else if side = 3 then
    w 0 = w 5 ∧ w 1 = w 2 ∧ w 3 = w 4
  else
    w 0 = w 5 ∧ w 1 = w 4 ∧ w 2 = w 3
  deriving Decidable

end HexagonPlanarPairing

/-- The cyclic three-colour word which separates the hexagon fibre from all
five planar pairing caps. -/
def hexagonColorWord (a b c d e f : Color) : Fin 6 → Color :=
  fun i =>
    if i = 0 then a else if i = 1 then b else if i = 2 then c
    else if i = 3 then d else if i = 4 then e else f

def cyclicThreeHexagonWord : HexagonBoundaryWord :=
  hexagonColorWord red blue purple red blue purple

/-- Its unique internal hexagon colouring. -/
def cyclicThreeHexagonColoring : HexagonInternalColoring :=
  hexagonColorWord purple red blue purple red blue

/-- The displayed internal colouring really extends the cyclic boundary word. -/
theorem cyclicThreeHexagonColoring_isExtension :
    IsHexagonExtension cyclicThreeHexagonWord
      cyclicThreeHexagonColoring := by
  decide

/-- The cyclic word has exactly one proper extension. -/
theorem card_hexagonExtensions_cyclicThree :
    (hexagonExtensions cyclicThreeHexagonWord).card = 1 := by
  decide

/-- None of the five noncrossing planar pairing caps is compatible with the
cyclic boundary word. -/
theorem cyclicThreeHexagonWord_no_planarPairing :
    ∀ side : HexagonPlanarPairing,
      ¬ side.Compatible cyclicThreeHexagonWord := by
  decide

/-- A converse sharpness witness: this word is accepted by one planar pairing
cap although it has no proper hexagon extension. -/
def pairedUnextendableHexagonWord : HexagonBoundaryWord :=
  hexagonColorWord red red blue red red blue

theorem pairedUnextendableHexagonWord_has_planarPairing :
    (1 : HexagonPlanarPairing).Compatible pairedUnextendableHexagonWord := by
  decide

theorem pairedUnextendableHexagonWord_no_extension :
    hexagonExtensions pairedUnextendableHexagonWord = ∅ := by
  decide

/-- Even at the level of support, hexagon extension is not equivalent to
compatibility with one of the five planar pairing caps. -/
theorem no_hexagon_planarPairing_support_identity :
    ¬ ∀ w : HexagonBoundaryWord,
      (∃ x, IsHexagonExtension w x) ↔
        ∃ side : HexagonPlanarPairing, side.Compatible w := by
  intro h
  have hcyclic := (h cyclicThreeHexagonWord).mp
    ⟨cyclicThreeHexagonColoring,
      cyclicThreeHexagonColoring_isExtension⟩
  rcases hcyclic with ⟨side, hside⟩
  exact cyclicThreeHexagonWord_no_planarPairing side hside

/-- A fixed nonnegative weighting of the five planar caps, written without a
list representation so that the obstruction remains a tiny kernel reduction. -/
def planarPairingWeightedCount
    (weight : HexagonPlanarPairing → Nat) (w : HexagonBoundaryWord) : Nat :=
  (if (0 : HexagonPlanarPairing).Compatible w then weight 0 else 0) +
  (if (1 : HexagonPlanarPairing).Compatible w then weight 1 else 0) +
  (if (2 : HexagonPlanarPairing).Compatible w then weight 2 else 0) +
  (if (3 : HexagonPlanarPairing).Compatible w then weight 3 else 0) +
  (if (4 : HexagonPlanarPairing).Compatible w then weight 4 else 0)

@[simp] theorem planarPairingWeightedCount_cyclicThree
    (weight : HexagonPlanarPairing → Nat) :
    planarPairingWeightedCount weight cyclicThreeHexagonWord = 0 := by
  simp [planarPairingWeightedCount,
    cyclicThreeHexagonWord_no_planarPairing]

/-- No nonnegative linear combination of the five planar pairing-cap counts
is the exact hexagon extension count.  The cyclic witness makes every cap
term zero while the hexagon count is one. -/
theorem no_weighted_planarPairing_hexagon_count_identity :
    ¬ ∃ weight : HexagonPlanarPairing → Nat,
      ∀ w : HexagonBoundaryWord,
        (hexagonExtensions w).card = planarPairingWeightedCount weight w := by
  rintro ⟨weight, hweight⟩
  have h := hweight cyclicThreeHexagonWord
  rw [card_hexagonExtensions_cyclicThree,
    planarPairingWeightedCount_cyclicThree] at h
  omega

end Mettapedia.GraphTheory.FourColor
