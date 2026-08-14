import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenu

/-!
# Seed-zero descent for annular frontier reductions

Addendum XXV begins its minimal-counterexample argument by applying a local
reduction and observing that a zero Menu-B seed count descends to the smaller
frontier.  This file states that assertion at the literal fiber level, across
possibly different finite graphs.

The construction deliberately asks for a reflection of actual Menu-B seeds,
rather than an equality of raw coloring counts.  A rotor, digon, two-cut, or
square construction must still provide such a reflection from its own
coloring/gluing theorem.  Thus this module is the common target for those
source reductions, not a substitute for constructing any of them.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}
variable {W : Type v} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  {reducedOuterCount : Nat}

noncomputable section

/-- The literal seed-reflection condition for one source reduction.  Every
Menu-B coloring of the reduced fixed-word fiber must lift to a Menu-B coloring
of the original fixed-word fiber.  This is the direction needed to carry a
zero seed count into the smaller object. -/
def AnnularFrontierMenuBSeedReflection
    (sourceData : AnnularBoundaryData G outerCount) (sourceWord : CAP5BoundaryWord)
    (reducedData : AnnularBoundaryData H reducedOuterCount)
    (reducedWord : CAP5BoundaryWord) : Prop :=
  ∀ reduced : { coloring : H.EdgeColoring Color //
      coloring ∈ annularFrontierTaitFiber reducedData reducedWord },
    AnnularFrontierMenuBState reducedData reduced.1 →
      ∃ source : { coloring : G.EdgeColoring Color //
          coloring ∈ annularFrontierTaitFiber sourceData sourceWord },
        AnnularFrontierMenuBState sourceData source.1

/-- A literal seed reflection makes zero Menu-B seed count descend from a
frontier counterexample to its reduction.  No count-product or count-sum is
assumed: those stronger source identities may be used later to construct the
reflection. -/
theorem annularFrontierMenuBSeedCount_eq_zero_of_seedReflection
    (sourceData : AnnularBoundaryData G outerCount) (sourceWord : CAP5BoundaryWord)
    (reducedData : AnnularBoundaryData H reducedOuterCount)
    (reducedWord : CAP5BoundaryWord)
    (hreflection : AnnularFrontierMenuBSeedReflection
      sourceData sourceWord reducedData reducedWord)
    (hzero : annularFrontierMenuBSeedCount sourceData sourceWord = 0) :
    annularFrontierMenuBSeedCount reducedData reducedWord = 0 := by
  rw [annularFrontierMenuBSeedCount_eq_zero_iff]
  intro coloring hfiber hmenu
  let reduced : { coloring : H.EdgeColoring Color //
      coloring ∈ annularFrontierTaitFiber reducedData reducedWord } :=
    ⟨coloring, hfiber⟩
  rcases hreflection reduced hmenu with ⟨source, hsourceMenu⟩
  exact (annularFrontierMenuBSeedCount_eq_zero_iff sourceData sourceWord).mp hzero
    source.1 source.2 hsourceMenu

/-- A fiber map is the usual concrete way a reduction proves seed reflection:
it sends every reduced coloring to an original coloring in the corresponding
fixed-word fiber. -/
theorem annularFrontierMenuBSeedCount_eq_zero_of_fiberMap
    (sourceData : AnnularBoundaryData G outerCount) (sourceWord : CAP5BoundaryWord)
    (reducedData : AnnularBoundaryData H reducedOuterCount)
    (reducedWord : CAP5BoundaryWord)
    (lift : { coloring : H.EdgeColoring Color //
        coloring ∈ annularFrontierTaitFiber reducedData reducedWord } →
      { coloring : G.EdgeColoring Color //
        coloring ∈ annularFrontierTaitFiber sourceData sourceWord })
    (hlift : ∀ reduced,
      AnnularFrontierMenuBState reducedData reduced.1 →
        AnnularFrontierMenuBState sourceData (lift reduced).1)
    (hzero : annularFrontierMenuBSeedCount sourceData sourceWord = 0) :
    annularFrontierMenuBSeedCount reducedData reducedWord = 0 := by
  apply annularFrontierMenuBSeedCount_eq_zero_of_seedReflection
    sourceData sourceWord reducedData reducedWord
  · intro reduced hmenu
    exact ⟨lift reduced, hlift reduced hmenu⟩
  · exact hzero

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor
