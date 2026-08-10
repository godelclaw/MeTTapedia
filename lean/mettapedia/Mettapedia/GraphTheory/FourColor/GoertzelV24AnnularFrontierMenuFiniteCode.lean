import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuProfileFactor

/-!
# One finite profile code for annular Menu-B fibers

For a fixed inner word, Addendum XXV asks whether a Tait coloring realizes a
Menu-B state.  The source's `Count` profile records a finite connectivity
pairing at every tracked color pair.  This file packages those computed
pairings into one finite code and proves that equality of the code preserves
the Menu-B predicate on the literal fiber.

The code contains no chosen configuration data: every coordinate is computed
from the coloring's selected-pair support graph.  It is deliberately only the
connectivity coordinate needed by Menu B; a corridor construction must later
provide the remaining boundary-color and capped-face coordinates of `Count`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The complete selected-pair connectivity coordinate of the source profile
at a fixed CAP5 word.  Its carriers depend only on that word, so one code is
shared by every coloring in the literal fiber at `word`. -/
abbrev AnnularFrontierMenuConnectionCode (word : CAP5BoundaryWord) :=
  (first second : Color) →
    Finset
      (AnnularFrontierWordPairPort word first second ×
        AnnularFrontierWordPairPort word first second)

/-- Compute the full finite Menu-B connectivity code of one coloring at a
fixed inner word. -/
noncomputable def annularFrontierMenuConnectionCode
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (word : CAP5BoundaryWord)
    (hword : data.innerBoundaryWord coloring = word) :
    AnnularFrontierMenuConnectionCode word :=
  fun first second =>
    annularFrontierWordPairConnectionProfile
      data hdata coloring word hword first second

/-- The Menu-B connectivity state space is genuinely finite.  This is a
small generated profile carrier, not a catalogue: `Color`, the five cap
ports, and every `Finset` coordinate are finite by construction. -/
theorem annularFrontierMenuConnectionCode_finite
    (word : CAP5BoundaryWord) :
    Finite (AnnularFrontierMenuConnectionCode word) := by
  classical
  infer_instance

omit [DecidableEq V] in
/-- On a fixed source fiber, extract the word equality required to compute
the common finite Menu-B code. -/
theorem annularFrontierMenuFiber_innerBoundaryWord_eq
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord)
    (coloring : { coloring : G.EdgeColoring Color //
      coloring ∈ annularFrontierTaitFiber data word }) :
    data.innerBoundaryWord coloring.1 = word :=
  (mem_annularFrontierTaitFiber_iff data word coloring.1).mp coloring.2 |>.2

/-- The profile code attached to a literal coloring in the source fiber. -/
noncomputable def annularFrontierMenuFiberConnectionCode
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord)
    (coloring : { coloring : G.EdgeColoring Color //
      coloring ∈ annularFrontierTaitFiber data word }) :
    AnnularFrontierMenuConnectionCode word :=
  annularFrontierMenuConnectionCode data hdata coloring.1 word
    (annularFrontierMenuFiber_innerBoundaryWord_eq data word coloring)

/-- Equality of the one finite connectivity code preserves the source's
Menu-B predicate.  This is the fiber-level factorization required before a
corridor profile repeat can be used in the Seed-Lemma descent. -/
theorem annularFrontierMenuBState_iff_of_fiberConnectionCode_eq
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord)
    (left right : { coloring : G.EdgeColoring Color //
      coloring ∈ annularFrontierTaitFiber data word })
    (hcode : annularFrontierMenuFiberConnectionCode data hdata word left =
      annularFrontierMenuFiberConnectionCode data hdata word right) :
    AnnularFrontierMenuBState data left.1 ↔
      AnnularFrontierMenuBState data right.1 := by
  apply annularFrontierMenuBState_iff_of_wordConnectionProfiles_eq
    data hdata left.1 right.1 word
    (annularFrontierMenuFiber_innerBoundaryWord_eq data word left)
    (annularFrontierMenuFiber_innerBoundaryWord_eq data word right)
  intro first second
  exact congrFun (congrFun hcode first) second

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor
