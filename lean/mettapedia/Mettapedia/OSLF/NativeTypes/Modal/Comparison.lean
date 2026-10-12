import Mettapedia.OSLF.NativeTypes.Modal.Rules

open Mettapedia.OSLF.Framework

/-!
# Comparison with the existential rely-possibly comprehension

The hypercube paper gives an existential postcondition on a reduct. The
specified-contractum semantics refines it by retaining the declaration's
right-hand side and its dependent certificate. This comparison uses the
independent generated operational relation, not an equality of definitions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Comparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules

universe u

/-- The paper's independent existential comprehension, with the matched
assignment retained in the ambient context and the rely inputs varying. -/
def ExistentialInhabits {plan : Plan} (schema : Schema plan)
    (A : String → ContextualValue → Prop) (B : Continuation.{u}) (term : Pattern) : Prop :=
  HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier ∧
  ∃ anchor : Assignment,
    GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) schema.context anchor ∧
    (∀ name ∈ schema.matchedNames, ∃ value, lookup anchor name = some value) ∧
    ∀ assignment, TypedRequest schema A anchor assignment →
      ∃ source target, schema.fill? assignment term = some source ∧
        (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step source target ∧
        Nonempty (substituteContinuation B assignment target)

/-- The strongest general elimination at the existential meaning has an
actual successor carrying the substituted continuation. Its endpoint is not
identified with the selected declaration's right-hand side. -/
theorem canonical_m_step_elim {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (inhabited : ExistentialInhabits schema A B term) :
    ∃ anchor : Assignment,
      GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) schema.context anchor ∧
      (∀ name ∈ schema.matchedNames, ∃ value, lookup anchor name = some value) ∧
      ∀ assignment, TypedRequest schema A anchor assignment →
        ∃ source target, schema.fill? assignment term = some source ∧
          (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step source target ∧
          Nonempty (substituteContinuation B assignment target) := by
  obtain ⟨_, anchor, typed, present, outcomes⟩ := inhabited
  exact ⟨anchor, typed, present, outcomes⟩

theorem canonical_carrier {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (inhabited : ExistentialInhabits schema A B term) :
    HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier :=
  inhabited.1

/-- Every exact inhabitant has the paper's existential postcondition. The
converse is separated by an actual authored-language counterexample. -/
theorem specified_implies_existential {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (inhabited : Inhabits schema A B term) : ExistentialInhabits schema A B term := by
  obtain ⟨implementation⟩ := inhabited
  refine ⟨implementation.carrier, implementation.anchor, implementation.anchorTyped,
    implementation.anchorPresent, ?_⟩
  intro assignment request
  let outcome := implementation.respond assignment request
  exact ⟨outcome.source, outcome.target, outcome.filling,
    ⟨outcome.receipt.representative, outcome.receipt.firing, outcome.valid.1.equivalent,
      outcome.valid.2, outcome.targetConversion⟩, ⟨outcome.certificate⟩⟩

end Mettapedia.OSLF.NativeTypes.Modal.Comparison
