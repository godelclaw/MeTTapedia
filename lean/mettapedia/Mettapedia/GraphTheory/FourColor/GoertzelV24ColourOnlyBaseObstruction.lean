import Mettapedia.GraphTheory.FourColor.VertexCodeTerminalAcceptance

/-!
# Why the finite base needs Euler-mass information

The direct vertex-code evaluator has two closed, connected, colourable runs
with identical boundary-colour support, face permutation, and cut state.
One is planar and accepted; its handled twin is not. Thus no terminal test
invariant under these three coordinates can equal the physical accepting
predicate on every run.

This is a kernel-checked obstruction to a base automaton that discards the
Euler mass while keeping only those three state coordinates. It does not
refute an automaton with another planarity-sensitive coordinate, and it does
not settle the finite-base obligation.
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

/-- The two closed runs also have the same face permutation (the unique
permutation of the empty interface) and the same cut-connectivity state.
Only the exact Euler mass distinguishes their terminal geometry. -/
theorem same_state_without_mass :
    (evaluate (twoStars true)).colours =
        (evaluate (twoStars false)).colours ∧
      (evaluate (twoStars true)).face =
        (evaluate (twoStars false)).face ∧
      (evaluate (twoStars true)).cuts =
        (evaluate (twoStars false)).cuts := by
  exact ⟨same_colour_support, Subsingleton.elim _ _, same_cut_data⟩

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

/-- No terminal test that discards only the Euler-mass coordinate can
recognize physical acceptance on all closed runs. Thus a finite structural
carrier must retain mass information (or an equivalent planarity invariant)
after colours, face boundary permutation, and cut profiles are known. -/
theorem no_mass_free_terminal_test :
    ¬ ∃ test : State (Fin 0) (Fin 0) → Bool,
        (∀ s t, s.colours = t.colours → s.face = t.face →
          s.cuts = t.cuts → test s = test t) ∧
        (∀ trace : Trace 0, test (evaluate trace) = Accepts trace) := by
  rintro ⟨test, hinvariant, hagree⟩
  obtain ⟨hcolour, hface, hcuts⟩ := same_state_without_mass
  have hsame := hinvariant (evaluate (twoStars true))
    (evaluate (twoStars false)) hcolour hface hcuts
  rw [hagree (twoStars true), hagree (twoStars false),
    flat_accepted, twisted_rejected] at hsame
  cases hsame

end Mettapedia.GraphTheory.FourColor.GoertzelV24ColourOnlyBaseObstruction
