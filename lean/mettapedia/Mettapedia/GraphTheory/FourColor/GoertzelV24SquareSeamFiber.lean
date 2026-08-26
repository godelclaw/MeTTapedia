import Mettapedia.GraphTheory.FourColor.GoertzelV24Square

/-!
# Seam-equal square words are colourable

The colouring lift takes the square's four edges from a local colouring, and
that local colouring has to be a proper extension of the boundary word the lift
itself puts on the four outer edges.  Those outer colours are not arbitrary:
the two outer edges joined by a seam receive the same reduction colour, so the
induced word has equal colours on each joined pair.

Such a word is never of the opposite-pair type, which is the only obstructed
one, so the fibre is nonempty and a local colouring is available.  The two
joined pairs are `0,1` with `2,3` for one planar reduction and `1,2` with
`3,0` for the other, matching the two adjacent-pair word types exactly.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SquareSeamFiber

set_option maxRecDepth 100000

open SquareBoundaryWord

/-- A word whose joined pairs agree is all-equal or of the matching
adjacent-pair type; in particular it is not an opposite-pair word. -/
theorem allEqual_or_adjacentPairs_of_pairEqual :
    ∀ w : SquareBoundaryWord,
      ((w 0 = w 1 ∧ w 2 = w 3) ∨ (w 1 = w 2 ∧ w 3 = w 0)) →
        w.AllEqual ∨ w.AdjacentPairs := by
  decide

/-- A seam-equal word is never obstructed. -/
theorem not_oppositePairs_of_pairEqual :
    ∀ w : SquareBoundaryWord, w.Nonzero →
      ((w 0 = w 1 ∧ w 2 = w 3) ∨ (w 1 = w 2 ∧ w 3 = w 0)) →
        ¬ w.OppositePairs := by
  decide

/-- **The fibre over a seam-equal word is nonempty.**  So the lift always has a
local colouring of the square available to it. -/
theorem squareExtensions_nonempty_of_pairEqual :
    ∀ w : SquareBoundaryWord, w.Nonzero →
      ((w 0 = w 1 ∧ w 2 = w 3) ∨ (w 1 = w 2 ∧ w 3 = w 0)) →
        (squareExtensions w).Nonempty := by
  decide

/-- The chosen local colouring of the square over a seam-equal word. -/
noncomputable def seamFibre (w : SquareBoundaryWord) (hw : w.Nonzero)
    (hpair : (w 0 = w 1 ∧ w 2 = w 3) ∨ (w 1 = w 2 ∧ w 3 = w 0)) :
    SquareInternalColoring :=
  (squareExtensions_nonempty_of_pairEqual w hw hpair).choose

theorem seamFibre_mem (w : SquareBoundaryWord) (hw : w.Nonzero)
    (hpair : (w 0 = w 1 ∧ w 2 = w 3) ∨ (w 1 = w 2 ∧ w 3 = w 0)) :
    seamFibre w hw hpair ∈ squareExtensions w :=
  (squareExtensions_nonempty_of_pairEqual w hw hpair).choose_spec

/-- The chosen local colouring is a proper extension of the word. -/
theorem isSquareExtension_seamFibre (w : SquareBoundaryWord) (hw : w.Nonzero)
    (hpair : (w 0 = w 1 ∧ w 2 = w 3) ∨ (w 1 = w 2 ∧ w 3 = w 0)) :
    IsSquareExtension w (seamFibre w hw hpair) :=
  mem_squareExtensions_iff.1 (seamFibre_mem w hw hpair)

end GoertzelV24SquareSeamFiber

end Mettapedia.GraphTheory.FourColor
