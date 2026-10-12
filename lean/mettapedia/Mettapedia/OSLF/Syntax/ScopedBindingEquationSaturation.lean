import Mettapedia.OSLF.Syntax.ScopedBindingEquationEvents
import Mettapedia.GSLT.Logic.IndexedContextActionQuotient

/-!
# Saturated behavioral congruence for permitted binding events modulo equations

The actual authored equation classes and complete scoped paths supply the
context action. Permitted occurrences supply the operational events, retaining
their root assignments and opened binder contexts. The greatest saturated
relation is the largest event bisimulation closed under all these context
actions, with arbitrary independently supplied observations.

The semantic quotient of context actions gives the same behavior. This is
not a higher-order GSOS admission theorem, an executable equation matcher,
or a proof that raw minimal-context criteria descend through the equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEquationSaturation

open _root_.CategoryTheory ScopedEncoding ScopedEquationContexts ScopedEquationEvents
open Mettapedia.GSLT IndexedContextEventSaturation

universe r a

variable {S : Signature} {M : List (MetaArity S)} {Index : Type r}
  (E : List (EqAxiom S M)) (rules : Index → UnpositionedRewrite (withMetas S M))
  (permission : PositionPermission S)
  {Atom : ContextCategory S → Type a}
  (observations : {scope : ContextCategory S} → Atom scope → State E scope → Prop)

local instance : Quiver (Scope S) := bindingFrameQuiver S

def dynamics : Data (action E) (Event rules permission) Atom where
  source := Event.sourceClass E
  target := Event.targetClass E
  observes := observations

/-- An exact quotient event support criterion at every variable context and sort. -/
theorem step_iff_event {scope : ContextCategory S} (before after : State E scope) :
    (dynamics E rules permission observations).Step before after ↔
      ∃ event : Event rules permission scope,
        event.sourceClass E = before ∧ event.targetClass E = after := Iff.rfl

/-- Every permitted occurrence gives the actual saturated identity-label step. -/
theorem event_supplies_step {scope : Scope S} (event : Event rules permission scope) :
    (dynamics E rules permission observations).Step (event.sourceClass E) (event.targetClass E) :=
  ⟨event, rfl, rfl⟩

/-- All declared binding interfaces, variable positions and stored siblings
participate in the earned contextual congruence. -/
theorem context_congruence {source target : Scope S} {left right : State E source}
    (related : (dynamics E rules permission observations).Bisimilar source left right)
    (context : BindingContext S source target) :
    (dynamics E rules permission observations).Bisimilar target
      (fillClass E context left) (fillClass E context right) :=
  (dynamics E rules permission observations).context_congruent related context

theorem largest_contextual_bisimulation {scope : Scope S} (left right : State E scope) :
    (dynamics E rules permission observations).Bisimilar scope left right ↔
      ∃ relation,
        (dynamics E rules permission observations).ReductionBisimulation relation ∧
        Data.ContextClosed (states := action E) relation ∧ relation scope left right :=
  (dynamics E rules permission observations).bisimilar_iff_contextual left right

/-- The comparison includes all quotient labels and all their raw scoped
representatives, not only labels already seen in a supplied execution. -/
theorem quotient_contexts_same_behavior {scope : Scope S} (left right : State E scope) :
    (IndexedContextActionQuotient.quotientData (dynamics E rules permission observations)).Bisimilar
        ((IndexedContextActionQuotient.projection (action E)).obj scope) left right ↔
      (dynamics E rules permission observations).Bisimilar scope left right :=
  IndexedContextActionQuotient.bisimilar_iff (states := action E)
    (dynamics E rules permission observations) (interface := scope) left right

/-- Capture-avoiding reindexing retains an actual occurrence and its exact
new source and target classes. It is not inferred from approximate observations. -/
theorem substituted_event_step {scope : Scope S} (event : Event rules permission scope)
    (destination : Ctx S) (sigma : Sub S scope.1 destination) :
    (dynamics E rules permission observations).Step (interface := (destination, scope.2))
      (bindQ sigma (event.sourceClass E)) (bindQ sigma (event.targetClass E)) := by
  refine ⟨event.map destination sigma, ?_, ?_⟩
  · exact Event.sourceClass_map E destination sigma event
  · exact Event.targetClass_map E destination sigma event

end Mettapedia.OSLF.Binding.ScopedEquationSaturation
