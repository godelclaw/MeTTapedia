import Mettapedia.OSLF.NativeTypes.Instances.Natural.Authored
import Mettapedia.OSLF.NativeTypes.Executable.InfiniteSourceControls

/-!
# Incoming observations distinguish the authored ambient carrier

Counter states are closed under outgoing execution. The full authored term
carrier additionally contains eliminators, and a zero eliminator can return a
counter state. Its incoming edge has no counterpart in the natural-successor
system. Thus the existing complete outgoing observation cannot be promoted to
incoming coverage or arbitrary two-direction formula transport.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.AuthoredBoundaryControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.GSLT.LanguageDef.Examples

def eliminatorBeforeZero : Pattern :=
  .apply "NatEliminate" [.fvar "motive", NativeNaturalCounter.counter 0,
    .fvar "step", .apply "NZero" []]

theorem eliminator_rootReducts :
    rootReducts Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language eliminatorBeforeZero =
      [NativeNaturalCounter.counter 0] := by
  simp [rootReducts, NativeNaturalCounter.rewrite_rows, eliminatorBeforeZero,
    matchPattern, matchArgs, mergeBindings, applyBindings]

theorem eliminator_steps_to_counter_zero (base : BasePremiseEvaluator) :
    Step base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language eliminatorBeforeZero
      (NativeNaturalCounter.counter 0) := by
  rw [step_iff_mem_rootReducts base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language
    NativeNaturalCounter.unconditional, eliminator_rootReducts]
  exact List.mem_singleton_self _

theorem eliminator_not_a_counter (number : Nat) :
    eliminatorBeforeZero ≠ NativeNaturalCounter.counter number := by
  simp [eliminatorBeforeZero, NativeNaturalCounter.counter]

def incomingEdge (base : BasePremiseEvaluator) : (gsltSpan (Authored.theory base)).Edge :=
  ⟨eliminatorBeforeZero, NativeNaturalCounter.counter 0,
    eliminator_steps_to_counter_zero base⟩

theorem authored_observation_no_incoming_coverage (base : BasePremiseEvaluator) :
    ¬ (Authored.observation base).TargetLifts := by
  intro covers
  obtain ⟨number, ends, _⟩ := covers 0 (incomingEdge base) rfl
  exact Nat.succ_ne_zero number ends

theorem authored_zero_has_predecessor (base : BasePremiseEvaluator) :
    ¬ satisfies (transitionSystem (gsltSpan (Authored.theory base)))
      (fun index : Fin 0 => index.elim0) (.box .past .ff)
      (NativeNaturalCounter.counter 0) := by
  intro holds
  exact holds eliminatorBeforeZero ⟨incomingEdge base, rfl, rfl⟩

/-- The same closed native formula distinguishes the represented natural
state from its image in the larger authored carrier. -/
theorem incoming_formula_separates (base : BasePremiseEvaluator) :
    satisfies (transitionSystem Counter.counter) (fun index : Fin 0 => index.elim0)
      (.box .past .ff) 0 ∧
    ¬ satisfies (transitionSystem (gsltSpan (Authored.theory base)))
      (fun index : Fin 0 => index.elim0) (.box .past .ff)
      (NativeNaturalCounter.counter 0) :=
  ⟨Executable.Finite.InfiniteSourceControls.source_zero_has_no_predecessor,
    authored_zero_has_predecessor base⟩

/-- Incoming failure leaves the proved complete outgoing interface intact. -/
theorem outgoing_without_incoming (base : BasePremiseEvaluator) :
    (Authored.observation base).SourceLifts ∧ ¬ (Authored.observation base).TargetLifts :=
  ⟨Authored.outgoing_coverage base, authored_observation_no_incoming_coverage base⟩

end Mettapedia.OSLF.NativeTypes.Instances.Natural.AuthoredBoundaryControls
