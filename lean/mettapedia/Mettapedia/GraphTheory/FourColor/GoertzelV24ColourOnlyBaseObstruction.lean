import Mettapedia.GraphTheory.FourColor.VertexCodeTerminalAcceptance

/-!
# Why the finite base needs structural state

The direct vertex-code evaluator has two closed, connected, colourable runs
with identical boundary-colour support. One is planar and accepted; its
handled twin is not. Thus no terminal test invariant under the colour
coordinate alone can equal the physical accepting predicate on every run.

This is a kernel-checked obstruction to a *colour-only* base automaton. It
does not refute an automaton that also tracks face, connectivity, or genus
information, and it does not settle the finite-base obligation.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24ColourOnlyBaseObstruction

open ExecutableJointTransfer ExecutableVertexCode VertexCodeTrace
open VertexCodeChecks VertexCodeTerminalAcceptance

set_option Elab.async false
set_option maxRecDepth 16000

/-- The planar and handled closed runs present precisely the same set of
boundary colour words. The carrier has no boundary positions, but the
equality is checked against the actual executable evaluator. -/
theorem same_colour_support :
    (evaluate (twoStars true)).colours =
      (evaluate (twoStars false)).colours := by
  decide +kernel

/-- No accepting test that factors through the colour coordinate can
recognize the direct physical terminal condition on all closed runs. -/
theorem no_colour_only_terminal_test :
    ¬ ∃ test : State (Fin 0) (Fin 0) → Bool,
        (∀ s t, s.colours = t.colours → test s = test t) ∧
        (∀ trace : Trace 0, test (evaluate trace) = Accepts trace) := by
  rintro ⟨test, hinvariant, hagree⟩
  have hsame := hinvariant (evaluate (twoStars true))
    (evaluate (twoStars false)) same_colour_support
  rw [hagree (twoStars true), hagree (twoStars false),
    flat_accepted, twisted_rejected] at hsame
  cases hsame

end Mettapedia.GraphTheory.FourColor.GoertzelV24ColourOnlyBaseObstruction
