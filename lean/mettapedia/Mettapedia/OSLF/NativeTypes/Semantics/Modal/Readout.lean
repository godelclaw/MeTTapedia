import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Root
import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Possibility

open Mettapedia.OSLF.Framework

/-!
# Native observational readout of complete modal responses

The native postcondition describes the equation class of the specified RHS
together with the substituted continuation. Each response of a full rely
family provides that native diamond observation through its actual receipt.
The full dependent continuation remains in the separately retained native
contractum family; its support predicate does not replace it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Modal

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.NativeEvidence
open GSLTTypeSynthesis

universe u

def contractumPredicate {plan : Plan} (schema : Schema plan)
    (assignment : ScopedRuleMatching.Assignment) (B : Continuation.{u}) :
    EquationPredicate (gslt plan schema.bound schema.programCarrier) :=
  saturatePredicate (gslt plan schema.bound schema.programCarrier)
    (fun target => schema.rhs? assignment = some target ∧ Nonempty (substituteContinuation B assignment target))

namespace Response

def nativePossibility {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : ScopedRuleMatching.Assignment} {B : Continuation.{u}}
    (outcome : Outcome schema term assignment B) :
    PossibilityFamily plan schema.bound schema.programCarrier
      (contractumPredicate schema assignment B) outcome.source :=
  PossibilityFamily.introduce ⟨outcome.receipt, outcome.valid⟩
    ⟨outcome.target, outcome.targetConversion, outcome.rhs, ⟨outcome.certificate⟩⟩

theorem canonical_native_diamond {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : ScopedRuleMatching.Assignment} {B : Continuation.{u}}
    (outcome : Outcome schema term assignment B) :
    (gsltOSLF (gslt plan schema.bound schema.programCarrier)).satisfies (S := ()) outcome.source
      (possibilityNativeType plan schema.bound schema.programCarrier
        (contractumPredicate schema assignment B)).pred :=
  possibility_family_support_iff.mp ⟨nativePossibility outcome⟩

theorem possibility_receipt_readout {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : ScopedRuleMatching.Assignment} {B : Continuation.{u}}
    (outcome : Outcome schema term assignment B) :
    (nativePossibility outcome).1.val = outcome.receipt ∧
      (nativePossibility outcome).1.val.firing.premiseHistory = outcome.receipt.firing.premiseHistory ∧
      (nativePossibility outcome).1.val.firing.job.site.address = outcome.receipt.firing.job.site.address :=
  ⟨rfl, rfl, rfl⟩

/-- The predicate readout and the original dependent native family retain
exactly the same physical occurrence, with the specified contractum beside it. -/
theorem dependent_native_comparison {plan : Plan} {schema : Schema plan} {term : Pattern}
    {assignment : ScopedRuleMatching.Assignment} {B : Continuation}
    (outcome : Outcome schema term assignment B) :
    (nativePossibility outcome).1 = outcome.native.1 ∧
      schema.rhs? assignment = some outcome.native.2.1 ∧
      Nonempty (substituteContinuation B assignment outcome.native.2.1) :=
  ⟨rfl, outcome.rhs, ⟨outcome.native.2.2.2⟩⟩

end Response

namespace Family

def nativeResponse {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation} {term : Pattern}
    (family : Family schema A B term) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A family.implementation.anchor assignment) :
    GeneralOccurrenceNativeReceipts.NativeFamily plan schema.bound schema.programCarrier
      (ContractumFamily schema assignment B) (family.response assignment request).source :=
  (family.response assignment request).native

def nativePossibilityResponse {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (family : Family schema A B term) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A family.implementation.anchor assignment) :
    PossibilityFamily plan schema.bound schema.programCarrier
      (contractumPredicate schema assignment B) (family.response assignment request).source :=
  Response.nativePossibility (family.response assignment request)

theorem all_responses_have_canonical_native_observations {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (family : Family schema A B term) :
    ∀ assignment request,
      (gsltOSLF (gslt plan schema.bound schema.programCarrier)).satisfies (S := ())
        (family.response assignment request).source
        (possibilityNativeType plan schema.bound schema.programCarrier
          (contractumPredicate schema assignment B)).pred :=
  fun assignment request => Response.canonical_native_diamond (family.response assignment request)

theorem nativeResponse_exact_contract {plan : Plan} {schema : Schema plan}
    {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation} {term : Pattern}
    (family : Family schema A B term) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A family.implementation.anchor assignment) :
    schema.fill? assignment family.representative = some (family.response assignment request).source ∧
      schema.rhs? assignment = some (family.nativeResponse assignment request).2.1 ∧
      (family.nativePossibilityResponse assignment request).1 = (family.nativeResponse assignment request).1 ∧
      (gslt plan schema.bound schema.programCarrier).Step
        (family.response assignment request).source (family.nativeResponse assignment request).2.1 ∧
      Nonempty (substituteContinuation B assignment (family.nativeResponse assignment request).2.1) := by
  have readout := family.response_readout assignment request
  exact ⟨readout.1, readout.2.1, rfl, readout.2.2.1, readout.2.2.2⟩

end Family

end Mettapedia.OSLF.NativeTypes.Semantics.Modal
