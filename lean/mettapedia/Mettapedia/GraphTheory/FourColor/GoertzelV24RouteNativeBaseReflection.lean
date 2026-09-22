import Mathlib.Data.Finset.Card
import Mettapedia.GraphTheory.FourColor.GoertzelV24ReductiveSpine

/-!
# Abstract base reflection: the audit joint for `BaseVerified`

`BaseVerified` quantifies over every object of bounded size. This historical
interface describes sufficient conditions for reducing it to a finite-state
audit. Despite its name, the structure alone does not enforce route-native
semantics: it permits an arbitrary state type, trace and predicate. Only the
reachable set is required to be finite. A concrete instantiation must supply
the mathematical connection to physical profiles.

Its historical closed-web consumer is marked as refuted in
`GoertzelV24SourceHeadlineAssembly`. This abstract interface neither repairs
that target nor discharges the current finite-base obligation.

This module records that joint at the spine level, fully proved, with the
three obligations separated:

* `trace` — how a bounded object presents itself as one finite state;
* `necessary_of_not_target` — a state-level condition every bounded
  counterexample forces on its own trace (the reflection/adequacy theorem);
* `trace_mem_reachable` — the trace lands in a supplied finite superset of
  realizable states (coverage; closure under transitions is not a field).

Once those are supplied, `BaseVerified` reduces to one decidable emptiness
check over the reachable set — a finite computation replayable through the
packed-payload discipline.  Nothing here constructs the trace, proves
adequacy, or computes the closure; those are the genuine remaining
mathematics, and this interface is where their results plug in.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ReductiveSpine

namespace ReductiveSystem

variable {Object : Type*} {target : Object → Prop}

/-- An abstract presentation of every bounded-size object as a state, with a
condition forced by counterexamples and a finite superset of actual traces.
No physical semantics or transition-closure property is required by this
structure. The entire carrier need not be finite. -/
structure RouteNativeBaseReflection
    (system : ReductiveSystem Object target)
    (State : Type*) where
  /-- The finite presentation of a bounded object. -/
  trace :
    (object : Object) → system.size object ≤ system.threshold → State
  /-- The state-level condition every bounded counterexample forces on its
  own trace.  This is the reflection/adequacy obligation: it must be proved
  from the object's actual geometry, not asserted. -/
  Necessary : State → Prop
  /-- A supplied finite superset of the traces of all bounded objects. -/
  reachable : Finset State
  trace_mem_reachable :
    ∀ (object : Object) (hsmall : system.size object ≤ system.threshold),
      trace object hsmall ∈ reachable
  necessary_of_not_target :
    ∀ (object : Object) (hsmall : system.size object ≤ system.threshold),
      ¬ target object → Necessary (trace object hsmall)

namespace RouteNativeBaseReflection

variable {system : ReductiveSystem Object target} {State : Type*}

/-- **The audit joint.**  If no reachable state satisfies the forced
condition, the base is verified: a bounded counterexample would force
`Necessary` on its own trace, and its trace is reachable. -/
theorem baseVerified_of_audit
    (reflection : RouteNativeBaseReflection system State)
    (haudit : ∀ state ∈ reflection.reachable, ¬ reflection.Necessary state) :
    system.BaseVerified := by
  intro object hsmall
  by_contra hbad
  exact haudit _ (reflection.trace_mem_reachable object hsmall)
    (reflection.necessary_of_not_target object hsmall hbad)

/-- The audit in its finite computational form: the filtered subset of
reachable states satisfying the forced condition is empty.  With a
decidable `Necessary` this is one replayable finite check. -/
theorem baseVerified_of_filter_eq_empty
    (reflection : RouteNativeBaseReflection system State)
    [DecidablePred reflection.Necessary]
    (haudit :
      reflection.reachable.filter reflection.Necessary = ∅) :
    system.BaseVerified := by
  refine reflection.baseVerified_of_audit ?_
  intro state hmem hnecessary
  have : state ∈ reflection.reachable.filter reflection.Necessary :=
    Finset.mem_filter.mpr ⟨hmem, hnecessary⟩
  simp [haudit] at this

/-- With the audit discharged, the universal target follows through the
existing spine equivalence: descent above the threshold, reflection audit
below it. -/
theorem target_all_of_audit
    (reflection : RouteNativeBaseReflection system State)
    (haudit : ∀ state ∈ reflection.reachable, ¬ reflection.Necessary state) :
    ∀ object, target object :=
  system.target_all_of_baseVerified
    (reflection.baseVerified_of_audit haudit)

end RouteNativeBaseReflection

end ReductiveSystem

end GoertzelV24ReductiveSpine

end Mettapedia.GraphTheory.FourColor
