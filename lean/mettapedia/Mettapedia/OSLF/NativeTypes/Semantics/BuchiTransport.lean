import Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
import Mettapedia.Logic.ModalMuCalculusBuchi

/-!
# Büchi path transport through covered observations

Outgoing endpoint coverage lifts an entire infinite path, choosing a source
successor at each step. Accepting observations are pulled back along the
state map. Neither carrier needs to be finite, and no predecessor-coverage
or preservation of event multiplicities is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open ModalFormula

universe u v e f
variable {X : Type u} {Y : Type v}
variable {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y}

/-- Mapping a source path preserves its accepting observations. -/
theorem path_preserved (observation : SpanMap A B) (accepting : Set Y) (source : X)
    (accepted : BuchiPath (transitionSystem A) .future
      (observation.states ⁻¹' accepting) source) :
    BuchiPath (transitionSystem B) .future accepting (observation.states source) := by
  obtain ⟨path, starts, edges, recurring⟩ := accepted
  refine ⟨observation.states ∘ path, congrArg observation.states starts, ?_, ?_⟩
  · intro index
    exact transition_preserved observation .future (edges index)
  · exact recurring

/-- Each observed step has a source lift at the current source state.
Dependent recursion retains this invariant for the entire infinite path. -/
theorem path_lifted (observation : SpanMap A B) (outgoing : observation.SourceLifts)
    (accepting : Set Y) (source : X)
    (accepted : BuchiPath (transitionSystem B) .future accepting (observation.states source)) :
    BuchiPath (transitionSystem A) .future (observation.states ⁻¹' accepting) source := by
  classical
  obtain ⟨path, starts, edges, recurring⟩ := accepted
  have nextWitness (index : Nat) (current : {state : X // observation.states state = path index}) :
      ∃ target, (transitionSystem A).trans current.1 .future target ∧
        observation.states target = path (index + 1) := by
    apply transition_lifted observation current.1 .future outgoing
    rw [current.2]
    exact edges index
  let lifted : (index : Nat) → {state : X // observation.states state = path index} :=
    Nat.rec ⟨source, starts.symm⟩ (fun index current =>
      ⟨(nextWitness index current).choose, (nextWitness index current).choose_spec.2⟩)
  refine ⟨fun index => (lifted index).1, rfl, ?_, ?_⟩
  · intro index
    exact (nextWitness index (lifted index)).choose_spec.1
  · intro lower
    obtain ⟨visit, after, acceptingVisit⟩ := recurring lower
    refine ⟨visit, after, ?_⟩
    change observation.states (lifted visit).1 ∈ accepting
    rw [(lifted visit).2]
    exact acceptingVisit

/-- Outgoing coverage is sufficient for exact existential Büchi path
transport, including from a finite observation to an infinite source. -/
theorem path_pullback (observation : SpanMap A B) (outgoing : observation.SourceLifts)
    (accepting : Set Y) (source : X) :
    BuchiPath (transitionSystem B) .future accepting (observation.states source) ↔
      BuchiPath (transitionSystem A) .future (observation.states ⁻¹' accepting) source :=
  ⟨path_lifted observation outgoing accepting source,
    path_preserved observation accepting source⟩

end Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport
