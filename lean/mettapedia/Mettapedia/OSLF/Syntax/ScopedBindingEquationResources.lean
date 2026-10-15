import Mettapedia.OSLF.Syntax.ScopedBindingEquationEvents
import Mettapedia.GSLT.Causality.ResourceFundingCompleteness
import Mathlib.Data.Multiset.Replicate

/-!
# Resource funding of actual scoped binding occurrences

The resource carrier stores complete equation-class program states. An
instance retains its authored index, opened binding context and actual
permitted event. It consumes its source state and produces its target state.
This is a linear presentation of the declared contextual reaction system,
not a molecular decomposition or a concrete execution backend.

A declared index price is unchanged by capture-avoiding substitution.
The funding theorem uses actual paid occurrence paths.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEquationResources

open ScopedEncoding ScopedEquationContexts ScopedEquationEvents
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe r

variable {S : Signature} {M : List (MetaArity S)} {Index : Type r}
  (E : List (EqAxiom S M))
  (rules : Index → UnpositionedRewrite (withMetas S M))
  (permission : PositionPermission S) (scope : Scope S)

def resources : System.{0, r} (State E scope) where
  Site := Index
  Instance index := {event : Event rules permission scope // event.index = index}
  consume firing := {firing.val.sourceClass E}
  read _ := 0
  produce firing := {firing.val.targetClass E}

def instanceOf (event : Event rules permission scope) :
    (resources E rules permission scope).Instance event.index := ⟨event, rfl⟩

theorem enabled_iff (marking : Multiset (State E scope))
    {index : Index} (firing : (resources E rules permission scope).Instance index) :
    (resources E rules permission scope).Enables marking firing ↔
      firing.val.sourceClass E ∈ marking := by
  simp only [System.Enables, resources, add_zero, Multiset.singleton_le]

noncomputable section

local instance : DecidableEq (State E scope) := Classical.decEq _

theorem singleton_fire (event : Event rules permission scope) :
    (resources E rules permission scope).fire {event.sourceClass E}
      (instanceOf E rules permission scope event) = {event.targetClass E} := by
  change ({event.sourceClass E} : Multiset (State E scope)) -
    {event.sourceClass E} + {event.targetClass E} = _
  rw [tsub_self, zero_add]

def occurrence (event : Event rules permission scope) :
    Occurrence (resources E rules permission scope).presentation
      ({event.sourceClass E} : Multiset (State E scope))
      ({event.targetClass E} : Multiset (State E scope)) :=
  ⟨event.index, ⟨instanceOf E rules permission scope event,
    (enabled_iff E rules permission scope _ _).mpr (Multiset.mem_singleton_self _),
    (singleton_fire E rules permission scope event).symm⟩⟩

def history (event : Event rules permission scope) :
    OccurrencePath (resources E rules permission scope).presentation
      ({event.sourceClass E} : Multiset (State E scope))
      ({event.targetClass E} : Multiset (State E scope)) :=
  .cons (occurrence E rules permission scope event) (.refl _)

def entry (event : Event rules permission scope) :
    (resources E rules permission scope).Entry :=
  ⟨event.index, instanceOf E rules permission scope event⟩

theorem history_entries (event : Event rules permission scope) :
    (resources E rules permission scope).pathEntries (history E rules permission scope event) =
      [entry E rules permission scope event] := rfl

def price (profile : Index → Nat) :
    ∀ {index : Index}, (resources E rules permission scope).Instance index → Multiset Unit :=
  fun {index} _ => Multiset.replicate (profile index) ()

def paid (profile : Index → Nat) : System (State E scope ⊕ Unit) :=
  funded (resources E rules permission scope) (price E rules permission scope profile)

def budget (amount : Nat) : Multiset Unit := Multiset.replicate amount ()

def AffordableHistory (profile : Index → Nat) (event : Event rules permission scope) (amount : Nat) :=
  ∃ path : OccurrencePath (paid E rules permission scope profile).presentation
    (marking {event.sourceClass E} (budget amount))
    (marking {event.targetClass E} (budget amount - budget (profile event.index))),
      (paid E rules permission scope profile).pathEntries path =
        [entry E rules permission scope event]

structure PaidHistory (profile : Index → Nat) (event : Event rules permission scope) (amount : Nat) where
  path : OccurrencePath (paid E rules permission scope profile).presentation
    (marking {event.sourceClass E} (budget amount))
    (marking {event.targetClass E} (budget amount - budget (profile event.index)))
  entries : (paid E rules permission scope profile).pathEntries path =
    [entry E rules permission scope event]

def PaidHistory.eventWord {profile : Index → Nat} {event : Event rules permission scope} {amount : Nat}
    (funding : PaidHistory E rules permission scope profile event amount) :
    List (Event rules permission scope) :=
  ((paid E rules permission scope profile).pathEntries funding.path).map fun entry => entry.2.val

theorem PaidHistory.eventWord_eq {profile : Index → Nat} {event : Event rules permission scope}
    {amount : Nat} (funding : PaidHistory E rules permission scope profile event amount) :
    funding.eventWord = [event] := by
  unfold PaidHistory.eventWord
  rw [funding.entries]
  rfl

theorem affordable_history_iff (profile : Index → Nat)
    (event : Event rules permission scope) (amount : Nat) :
    AffordableHistory E rules permission scope profile event amount ↔
      profile event.index ≤ amount := by
  have cost : historyPrice (resources E rules permission scope)
      (price E rules permission scope profile) [entry E rules permission scope event] =
        budget (profile event.index) := by
    change budget (profile event.index) + 0 = budget (profile event.index)
    exact add_zero _
  have executable := (resources E rules permission scope).fires_pathEntries
    (history E rules permission scope event)
  rw [history_entries] at executable
  have comparison := funded_history_iff (resources E rules permission scope)
    (price E rules permission scope profile) [entry E rules permission scope event]
    ({event.sourceClass E} : Multiset (State E scope))
    ({event.targetClass E} : Multiset (State E scope)) (budget amount)
  rw [cost] at comparison
  exact comparison.trans ((and_iff_right executable).trans (Multiset.replicate_le_replicate ()))

theorem paid_history_nonempty_iff (profile : Index → Nat)
    (event : Event rules permission scope) (amount : Nat) :
    Nonempty (PaidHistory E rules permission scope profile event amount) ↔
      profile event.index ≤ amount := by
  constructor
  · rintro ⟨funding⟩
    exact (affordable_history_iff E rules permission scope profile event amount).mp
      ⟨funding.path, funding.entries⟩
  · intro affordable
    obtain ⟨path, entries⟩ := (affordable_history_iff E rules permission scope profile event amount).mpr
      affordable
    exact ⟨⟨path, entries⟩⟩

theorem substitution_preserves_affordability (profile : Index → Nat)
    (event : Event rules permission scope) (destination : Ctx S)
    (sigma : Sub S scope.1 destination) (amount : Nat) :
    AffordableHistory E rules permission (destination, scope.2) profile
      (event.map destination sigma) amount ↔
        AffordableHistory E rules permission scope profile event amount := by
  rw [affordable_history_iff, affordable_history_iff]
  rfl

end

end Mettapedia.OSLF.Binding.ScopedEquationResources
